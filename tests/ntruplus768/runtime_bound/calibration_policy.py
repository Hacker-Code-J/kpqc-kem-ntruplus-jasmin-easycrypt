"""Source calibration is checked in addition to, never replaced by, source hashes.

Fresh regeneration is compared at executable-body and AST/fee level. Thus
reducing both a ghost counter and its proved bound cannot manufacture PASS.
"""
import json
from pathlib import Path
import re
import policy

MODEL_ID = 'owned-array-word-ram-v1'
REQUIRED_KINDS = ('fixed','primitive','wordchecks','sampling','kernels','sim','phase','outer')
CALIBRATION_FILES = tuple('tests/ntruplus768/runtime_bound/calibration/'+name for name in
    ('manifest.json','manual-kernels.json','manual-sim.json','manual-phase.json','manual-outer.json'))
ACTUAL_WORD_ENDPOINTS = tuple('ntruplus/proof/768/ref/kem_runtime_bound/NTRUPlus768RTWordReduction.ec:RTWord_'+name+'.run'
    for name in ('DI','DO','CO'))
MEASURED_WORD_ENDPOINTS = tuple(value[:-4]+'.measure' for value in ACTUAL_WORD_ENDPOINTS)
FINAL_THEOREMS = (
    ('NTRUPlus768RTFinal.ec','rt_original_runtime_bound'),
    ('NTRUPlus768RTCompleteCost.ec','rt_complete_bound_values'),
    ('NTRUPlus768RTCompleteCost.ec','rt_complete_di_cap'),
    ('NTRUPlus768RTCompleteCost.ec','rt_complete_do_cap'),
    ('NTRUPlus768RTCompleteCost.ec','rt_complete_co_cap'),
    ('NTRUPlus768RTCompleteCost.ec','rt_run_dispatcher_values'))

def path(value):
    p = policy.ROOT / value
    policy.require(not Path(value).is_absolute() and p.resolve().is_relative_to(policy.ROOT), 'calibration path outside checkout')
    policy.require(p.is_file() and not p.is_symlink(), 'calibration input missing or indirect: ' + value)
    return p


def code_mask(text):
    # Preserve byte offsets while masking nested comments and quoted names.
    out=list(text);depth=0;quoted=False;i=0
    while i<len(text):
        if not quoted and text.startswith('(*',i):
            depth+=1;out[i:i+2]=[' ',' '];i+=2;continue
        if depth and text.startswith('*)',i):
            depth-=1;out[i:i+2]=[' ',' '];i+=2;continue
        if depth:
            if text[i]!='\n':out[i]=' '
        elif text[i]=='"' and (i==0 or text[i-1]!='\\'):
            quoted=not quoted;out[i]=' '
        elif quoted and text[i]!='\n':out[i]=' '
        i+=1
    policy.require(depth==0 and not quoted,'unterminated calibration source token')
    return ''.join(out)


def raw_body(text,qualified):
    import model_contract
    parts=qualified.split('.')
    policy.require(len(parts) in (2,3),'endpoint must be [theory.]module.procedure')
    module,proc=parts[-2:];masked=code_mask(text)
    modules=list(re.finditer(r'\bmodule\s+(?!type\b)(\w+)\b',masked));matches=[]
    for index,m in enumerate(modules):
        if m.group(1)!=module:continue
        limit=modules[index+1].start() if index+1<len(modules) else len(masked)
        decl=re.search(r'(?m)^\s*(?:lemma|op|type|theory|require|import)\b',masked[m.end():limit])
        if decl:limit=m.end()+decl.start()
        opening=re.search(r'=\s*\{',masked[m.end():limit])
        if not opening:continue
        start=m.end()+opening.end()-1;end=model_contract.syntax.balanced_end(masked,start)
        block=masked[start+1:end-1]
        for name,header,_body,begin,finish in model_contract.syntax.procedures(block):
            if name==proc:
                inner=start+1+begin+len(header)
                matches.append(text[inner+1:start+1+finish-1])
    policy.require(len(matches)==1,'missing/ambiguous calibrated procedure: '+qualified)
    return matches[0]


def body(text,qualified):
    return policy.compact(raw_body(text,qualified))


def lemma_declaration(text,name):
    code=policy.without_comments(text)
    matches=re.findall(r'\blemma\s+'+re.escape(name)+r'\b(.*?)\bproof\s*\.',code,re.S)
    policy.require(len(matches)==1,'missing/ambiguous calibrated theorem: '+name)
    return policy.compact('lemma '+name+matches[0])


def fixed_declarations(group,proc,actual=None):
    import fee_checker
    source=path(group['source']).read_text()
    signature=fee_checker.source_procedure(source,proc['source_name'])
    args=','.join(signature['params'])
    pre='0<=W64.to_uint base<=768' if 'base' in signature['params'] else 'true'
    expected={
      proc['projection']:'lemma '+proc['projection']+' : equiv['+proc['generated_name']+' ~ '+proc['source_name']+' : ={'+args+'} ==> res{1}.`1=res{2}].',
      proc['cost_lemma']:'lemma '+proc['cost_lemma']+' : hoare['+proc['generated_name']+' : '+pre+' ==> 0<=res.`2<='+str(proc['cost'])+'].'}
    actual=path(group['generated_source']).read_text() if actual is None else actual
    for name,statement in expected.items():
        policy.require(lemma_declaration(actual,name)==policy.compact(statement),'calibration theorem endpoint/precondition/bound drift: '+name)


def compare_body(actual, regenerated, qualified):
    policy.require(body(actual, qualified)==body(regenerated, qualified), 'fresh generated executable body differs: '+qualified)


def compare_cost_record(expected, regenerated):
    # Proof script formatting may be revised, but the source-derived charges,
    # loop bounds, coverage and calibrated theorem bounds may not drift.
    fields=('name','source','source_sha256','generated_source','procedures')
    policy.require(all(expected.get(k)==regenerated.get(k) for k in fields), 'regenerated source/AST/charge record differs')


def manifest(require_complete=True):
    p=policy.TEST/'calibration/manifest.json'
    if not p.is_file():
        policy.require(not require_complete, 'source calibration manifest awaits reviewed freeze')
        return None
    data=json.loads(p.read_text())
    policy.require(data.get('schema')==1, 'unknown calibration schema')
    if require_complete:
        policy.require(data.get('status')=='FROZEN', 'source calibration is not frozen')
    policy.require(data.get('cost_model',{}).get('id')==MODEL_ID, 'unreviewed execution cost model')
    return data


def validate_coverage(audit, categories, observed):
    """Require all independently checked source strata and the reviewed final types."""
    policy.require(isinstance(audit,dict),'reviewed whole-runtime calibration audit is missing')
    policy.require(audit.get('model')==MODEL_ID,'whole-runtime cost model mismatch')
    policy.require(audit.get('required_calibration_kinds')==list(REQUIRED_KINDS),'calibration category omitted or changed')
    policy.require(set(categories)==set(REQUIRED_KINDS) and all(categories.values()),'actual-body calibration category incomplete')
    policy.require(set(audit.get('actual_word_endpoints',[]))==set(ACTUAL_WORD_ENDPOINTS),'actual final word endpoint inventory changed')
    policy.require(set(ACTUAL_WORD_ENDPOINTS)<=set(observed),'actual final word endpoint lacks source calibration')
    policy.require(set(MEASURED_WORD_ENDPOINTS)<=set(observed),'measured data/counter endpoint lacks source calibration')
    policy.require(set(audit.get('source_calibration_files',[]))==set(CALIBRATION_FILES),'source calibration input category omitted')
    records=audit.get('calibrated_final_theorems',[])
    required={('ntruplus/proof/768/ref/kem_runtime_bound/'+source,name) for source,name in FINAL_THEOREMS}
    actual={(item['source'],item['theorem']) for item in records}
    policy.require(required<=actual and len(actual)==len(records),'closed final cost theorem inventory omitted or duplicated')
    for item in records:
        source=path(item['source'])
        policy.require(source.parent==policy.PROOF,'calibrated final theorem outside new family')
        policy.require(lemma_declaration(source.read_text(),item['theorem'])==policy.compact(item['expected_declaration']),
                       'reviewed final calibrated theorem declaration drift: '+item['theorem'])
    return {'status':'COMPLETE_SOURCE_CALIBRATION','kinds':list(REQUIRED_KINDS),
            'actual_word_endpoints':list(ACTUAL_WORD_ENDPOINTS),
            'measured_word_endpoints':list(MEASURED_WORD_ENDPOINTS),
            'calibrated_final_theorems':[item['theorem'] for item in records]}


def check(require_complete=True, reviewed_manifest=None):
    data=manifest(require_complete)
    if data is None:
        import manual_calibration
        return {'status':'PENDING_CALIBRATION','full_cost_claim':False,'manual':manual_calibration.check(require_complete=False)}
    generator=data.get('generator',{})
    p=path(generator['source'])
    policy.require(policy.sha(p.read_bytes())==generator['sha256'], 'generator input pin drift')
    for support in generator.get('support_files',[]):
        policy.require(policy.sha(path(support['source']).read_bytes())==support['sha256'],'generator support pin drift')
    groups=data.get('groups',[])
    if require_complete:
        policy.require(groups, 'no calibrated fixed bodies')
    generated={str(p.relative_to(policy.ROOT)) for p in policy.PROOF.glob('NTRUPlus768RTFixed*.ec')
               if p.name!='NTRUPlus768RTFixedWordChecks.ec'}
    policy.require(generated=={group['generated_source'] for group in groups},
                   'fixed-body source calibration inventory omitted or extended')
    names=set(); endpoints=set(); reconstructed=[]
    import fee_checker
    for group in groups:
        reconstructed.append(fee_checker.check_group(group))
        policy.require(group['name'] not in names,'duplicate calibration group');names.add(group['name'])
        src=path(group['source']);target=path(group['generated_source'])
        policy.require(policy.sha(src.read_bytes())==group['source_sha256'],'calibrated original source changed')
        policy.require(policy.sha(target.read_bytes())==group['generated_source_sha256'],'calibrated generated source changed')
        for proc in group['procedures']:
            fixed_declarations(group,proc)
            key=(group['generated_source'],proc['generated_name'])
            policy.require(key not in endpoints,'duplicate calibration endpoint');endpoints.add(key)
            for name,file,keyhash in ((proc['source_name'],src,'source_body_sha256'),(proc['generated_name'],target,'generated_body_sha256')):
                policy.require(policy.sha(raw_body(file.read_text(),name).encode())==proc[keyhash],'procedure body pin drift')
            policy.require(proc.get('ast') and isinstance(proc.get('cost'),int) and proc['cost']>=0,'missing AST or source-derived bound')
            for theorem in ('projection','cost_lemma'):
                policy.require(re.search(r'\blemma\s+'+re.escape(proc[theorem])+r'\b',target.read_text()),'calibrated endpoint lacks named theorem')
    import manual_calibration
    manual=manual_calibration.check(require_complete=require_complete)
    import kernel_calibration
    kernels=kernel_calibration.check(require_complete=require_complete)
    import sim_calibration
    sim=sim_calibration.check(require_complete=require_complete)
    extras={}
    import importlib
    for name in ('phase','outer'):
        helper=policy.TEST/(name+'_calibration.py')
        if helper.is_file():
            extras[name]=importlib.import_module(name+'_calibration').check(require_complete=require_complete)
        else:
            policy.require(not require_complete,name+' source calibration checker is missing')
            extras[name]={'status':'PENDING','endpoints':[]}
    manual_endpoints=set(manual.get('endpoints',[]))
    categories={
        'fixed':len(groups)==12 and len(endpoints)==126,
        'primitive':sum(':RTPrimitive.' in value for value in manual_endpoints)==5,
        'wordchecks':sum(':RTFixedWordChecks.' in value for value in manual_endpoints)==2,
        'sampling':sum(':RTPsiSampler.' in value or ':RTKey32Sampler.' in value for value in manual_endpoints)==2,
        'kernels':kernels.get('status')=='KERNEL_SOURCE_FEES_RECONSTRUCTED',
        'sim':sim.get('status')=='SIM_SOURCE_FEES_RECONSTRUCTED',
        'phase':extras['phase'].get('status')=='PHASE_SOURCE_FEES_RECONSTRUCTED'
                and bool(extras['phase'].get('closed_prices'))
                and not re.search(r'DRAFT|PENDING',extras['phase'].get('scope','')),
        'outer':extras['outer'].get('status')=='OUTER_SOURCE_FEES_RECONSTRUCTED'
                and bool(extras['outer'].get('closed_bounds'))
                and set(extras['outer'].get('actual_word_endpoints',[]))==set(ACTUAL_WORD_ENDPOINTS)}
    observed={source+':'+name for source,name in endpoints}|manual_endpoints
    for item in (kernels,sim,*extras.values()):observed.update(item.get('endpoints',[]))
    external_inputs=[]
    for item in extras.values():
        for external in item.get('external_inputs',[]):
            source=Path(external['path'])
            policy.require(source.is_absolute() and source.is_file(),'calibration semantic support path missing')
            policy.require(policy.sha(source.read_bytes())==external['sha256'],'calibration semantic support pin drift')
            external_inputs.append(external)
    import composition_calibration
    composition=composition_calibration.check()
    coverage={'status':'DRAFT_SOURCE_COVERAGE','categories':categories}
    if require_complete:
        policy.require(isinstance(reviewed_manifest,dict),'reviewed proof manifest required for whole-cost gate')
        coverage=validate_coverage(reviewed_manifest.get('runtime_cost_audit'),categories,observed)
    return {'status':'CALIBRATION_SOURCE_CHECK_ONLY','groups':len(groups),'endpoints':len(endpoints),
            'manual':manual,'kernels':kernels,'sim':sim,**extras,'coverage':coverage,
            'composition':composition,'external_inputs':external_inputs,
            'independent_source_fees':reconstructed,'model':MODEL_ID,'fresh_regeneration':'NOT_REPLAYED'}


def replay(run, output):
    data=manifest(True); records=[]
    for index,group in enumerate(data['groups']):
        dest=Path(output)/'calibration-replay'/str(index);dest.mkdir(parents=True)
        produced=dest/'record.json'
        log=run('calibration-'+group['name'],[__import__('sys').executable,path(data['generator']['source']),group['name'],
            '--root',policy.ROOT,'--output-dir',dest,'--manifest',produced],cwd=dest)
        new=json.loads(produced.read_text());compare_cost_record(group,new)
        regenerated=dest/Path(group['generated_source']).name
        policy.require(regenerated.is_file(),'generator did not produce expected body')
        authored=path(group['generated_source']).read_text();fresh=regenerated.read_text()
        for proc in group['procedures']:
            compare_body(authored,fresh,proc['generated_name'])
        for name in re.findall(r'(?m)^\s*lemma\s+(\w+)',policy.without_comments(fresh)):
            policy.require(lemma_declaration(authored,name)==lemma_declaration(fresh,name),'fresh semantic declaration drift: '+name)
        records.append({'group':group['name'],'result':'PASS','record':str(produced),'record_sha256':policy.sha(produced.read_bytes()),
                        'generated_copy':str(regenerated),'generated_sha256':policy.sha(regenerated.read_bytes()),'log':str(log)})
    return records
