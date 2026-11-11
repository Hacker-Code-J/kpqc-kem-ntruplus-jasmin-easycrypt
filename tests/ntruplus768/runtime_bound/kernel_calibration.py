"""Reconstruct upper-wrapper charges from original typed bodies and closed callees."""
import ast,json,re
from pathlib import Path
import policy
import calibration_policy as cal
import manual_calibration as manual
import model_contract


def validate_type(text):
    from fee_checker import validate_type as native_type
    expanded=re.sub(r'\bpke_poly\b','W16.t Array768.t',text)
    expanded=re.sub(r'\boption\b','',expanded)
    native_type(expanded)


def type_cells(text):
    return sum(map(int,re.findall(r'Array(\d+)\.t',text)))+768*len(re.findall(r'\bpke_poly\b',text))


def signature(text,qualified):
    module,proc=qualified.split('.')[-2:]
    matches=[(header,body) for m,block in model_contract.syntax.modules(text) if m==module
             for name,header,body,_i,_j in model_contract.syntax.procedures(block) if name==proc]
    policy.require(len(matches)==1,'kernel signature missing: '+qualified)
    header,body=matches[0];opening=header.index('(')
    from fee_checker import closing
    end=closing(header,opening);parameters={}
    for group in header[opening+1:end].split(','):
        names,ty=group.split(':',1)
        for name in names.split():parameters[name]=ty.strip()
    ret=header[end+1:].strip().removeprefix(':').strip()
    policy.require(ret.endswith('='),'kernel result declaration malformed');ret=ret[:-1].strip()
    local=dict(parameters)
    for match in re.finditer(r'\bvar\s+([^:;]+):([^;]+);',body):
        for name in re.findall(r'\w+',match.group(1)):local[name]=match.group(2).strip()
    for ty in [*local.values(),ret]:validate_type(ty)
    return parameters,local,ret


def expression_ops(expr,variables):
    # Closed high-level wrapper fragment: options, tuple selectors,
    # scalar status comparisons and conjunctions. No pure cryptographic op.
    policy.require(isinstance(variables,dict),'kernel expression requires typed environment')
    for ty in variables.values():validate_type(ty)
    tokens=re.findall(r'[A-Za-z_]\w*(?:\.\w+)*',expr)
    allowed=set(variables)|{'Some','None','oget','true','false','witness','W32.zero','W64.zero'}
    policy.require(all(t in allowed for t in tokens),'unsupported kernel expression')
    remaining=re.sub(r'[A-Za-z_]\w*(?:\.\w+)*','',expr)
    remaining=re.sub(r'\.\`\d+','',remaining).replace('/\\','').replace('\\/','').replace('<>','')
    policy.require(not re.search(r'[^\s\d(),=]',remaining),'unsupported kernel expression operator')
    return len(re.findall(r'\b(?:Some|oget)\b',expr))+expr.count(',')+len(re.findall(r'<>|(?<![<>=])=(?![=>])|/\\|\\/|\.\`\d+',expr))


def numeric(expr,values):
    node=ast.parse('('+expr+')',mode='eval').body
    def walk(n):
        if isinstance(n,ast.Constant) and type(n.value)==int:return n.value
        if isinstance(n,ast.Name):policy.require(n.id in values,'unclosed cost symbol: '+n.id);return values[n.id]
        if isinstance(n,ast.BinOp) and isinstance(n.op,(ast.Add,ast.Mult)):
            a,b=walk(n.left),walk(n.right);return a+b if isinstance(n.op,ast.Add) else a*b
        raise ValueError('unsupported calibrated bound expression')
    return walk(node)


def statements(nodes,callees,types,values):
    original=[];measured=[];total=0
    for n in nodes:
        kind=n['kind']
        if kind=='call':
            c=callees[n['key']];args=n['args'].split(',')
            policy.require(len(args)==c['_arity'],'callee argument arity changed')
            selectors=expression_ops(n['args'],types)-n['args'].count(',')
            scratch=sum(type_cells(ty) for arg,ty in zip(args,c['_params'].values()) if arg.strip()=='witness')
            fee=2+len(args)+scratch+3*c['_cells']+selectors
            parts={'call_frame':2,'arguments':len(args),'scratch_cells':scratch,'result_clone':3*c['_cells'],'selector_ops':selectors}
            source=n['lhs']+'<@'+c['original']+'('+n['args']+');'
            measured.extend([n['temp']+'<@'+c['module']+'.'+c['proc']+'('+n['args']+');',
                n['lhs']+'<-'+n['temp']+'.`1;', 'rt_work<-rt_work+'+n['temp']+'.`2+'+str(fee)+';'])
            policy.require(c['bound'] in values,'callee bound is not calibrated: '+c['bound']);total+=fee+values[c['bound']]
            policy.require(n['selectors']==selectors,'selector omission')
        elif kind=='assign':
            expression=n['expr'];ops=expression_ops(expression,types)
            cells=0 if expression=='None' else type_cells(types[n['lhs']])
            fee=1+ops+3*cells;parts={'transfer':1,'expression_ops':ops,'result_clone':3*cells}
            source=n['lhs']+'<-'+expression+';';measured.extend([source,'rt_work<-rt_work+'+str(fee)+';']);total+=fee
            policy.require(n['cells']==cells and n['ops']==ops,'assignment payload/operation omission')
        elif kind=='if':
            guard=expression_ops(n['cond'],types);fee=1+guard;parts={'branch':1,'guard_ops':guard}
            nested,code,inner=statements(n['body'],callees,types,values)
            source='if('+n['cond']+'){'+nested+'}'
            measured.extend(['rt_work<-rt_work+'+str(fee)+';','if('+n['cond']+'){'+code+'}']);total+=fee+inner
        else:raise ValueError('unsupported kernel source block')
        policy.require(n['fee']==fee and n['fee_parts']==parts,'kernel charge formula differs from source')
        policy.require(policy.compact(n['source_statement'])==policy.compact(source),'kernel statement coverage differs')
        original.append(source)
    return ''.join(original),''.join(measured),total


def check(require_complete=True):
    record=policy.TEST/'calibration/manual-kernels.json'
    if not record.is_file():
        policy.require(not require_complete,'manual kernel calibration pending');return {'status':'PENDING','endpoints':[]}
    data=json.loads(record.read_text());leaf=cal.manifest(require_complete=False)
    policy.require(leaf is not None,'kernel calibration needs native leaves')
    originals={};values={};targets={}
    import fee_checker
    for group in leaf['groups']:
        fee_checker.check_group(group)
        text=cal.path(group['source']).read_text()
        for proc in group['procedures']:
            originals[proc['source_name']]=(text,proc['source_name'])
            targets[proc['generated_name']]=proc
        values['rt_fixed_'+group['name'].lower()+'_bound']=group['procedures'][-1]['cost']
    for group in leaf.get('manual_groups',[]):
        text=cal.path(group['source']).read_text()
        for proc in group['procedures']:
            originals[proc['source_name']]=(text,proc['source_name']);targets[proc['generated_name']]=proc
            manual_name=proc['generated_name'].split('.')[-1]
            expected_cost={'normalize':16133,'trit':14597}.get(manual_name)
            policy.require(expected_cost is not None and proc['cost']==expected_cost,'manual leaf bound differs from independent formula')
            values['rt_fixed_'+manual_name+'_bound']=expected_cost
    for p in data['procedures']:
        file=policy.BASE/p['file'];policy.require(file.is_file() and policy.sha(file.read_bytes())==p['source_sha256'],'manual kernel original source drift')
        originals[p['old']]=(file.read_text(),p['old'])
    internal={'RTKernel'+p['name']+'.run':p for p in data['procedures']}
    callees={key:dict(value) for key,value in data['callees'].items()}
    for c in callees.values():
        target=c['module']+'.'+c['proc']
        if target in targets:
            policy.require(targets[target]['source_name']==c['original'] and targets[target]['projection']==c['proof'],'native callee projection mapping changed')
        else:
            policy.require(target in internal and internal[target]['old']==c['original'],'uncalibrated kernel implementation substituted')
            base='rt_kernel_'+internal[target]['name'].lower()
            policy.require((c['bound'],c['proof'],c['cost'])==(base+'_bound',base+'_projection',base+'_cost'),'internal callee theorem mapping changed')
        policy.require(c['original'] in originals,'callee lacks source closure')
        source,qualified=originals[c['original']];params,_locals,ret=signature(source,qualified)
        c['_params']=params;c['_arity']=len(params);c['_cells']=type_cells(ret)
        policy.require(c['arity']==len(params) and c['cells']==type_cells(ret) and type_cells(c['ret'])==type_cells(ret),'callee signature/body type drift')
    actual=(policy.PROOF/'NTRUPlus768RTKernelCosts.ec').read_text();endpoints=[]
    for p in data['procedures']:
        source,qualified=originals[p['old']];params,types,ret=signature(source,qualified)
        policy.require(p['types']=={name:type_cells(ty) for name,ty in params.items()},'entry type coverage changed')
        entry=3*sum(type_cells(x) for x in params.values())
        returnfee=1+expression_ops(p['result'],types)+3*type_cells(ret)
        policy.require(p['entry']==entry and p['returnfee']==returnfee and p['cells']==type_cells(ret),'entry/return clone omission')
        original,code,local=statements(p['body'],callees,types,values)
        original+='return '+p['result']+';'
        policy.require(manual.normalize(cal.raw_body(source,qualified))==policy.compact(original),'original kernel statement coverage incomplete')
        expected='rt_work<-'+str(entry)+';'+code+'rt_work<-rt_work+'+str(returnfee)+';return('+p['result']+',rt_work);'
        endpoint='RTKernel'+p['name']+'.run'
        manual_body=cal.raw_body(actual,endpoint)
        policy.require(manual.normalize(manual_body)==policy.compact(expected),'measured kernel source charges differ')
        value=entry+local+returnfee;policy.require(numeric(p['bound'],values)==value,'composed kernel bound differs')
        bound='rt_kernel_'+p['name'].lower()+'_bound'
        found=re.search(r'\bop\s+'+bound+r'\s*:\s*int\s*=([^.]*)\.',actual)
        policy.require(found and policy.compact(found.group(1))==policy.compact(p['bound']),'actual kernel bound operation drift')
        cost='rt_kernel_'+p['name'].lower()+'_cost';projection='rt_kernel_'+p['name'].lower()+'_projection'
        expected_cost='lemma '+cost+': hoare['+endpoint+': true ==>0<=res.`2<='+bound+'].'
        expected_projection='lemma '+projection+': equiv['+endpoint+'~'+p['old']+': ={'+','.join(sorted(params))+'} ==>res{1}.`1=res{2}].'
        policy.require(cal.lemma_declaration(actual,cost)==policy.compact(expected_cost),'kernel Hoare contract drift')
        policy.require(cal.lemma_declaration(actual,projection)==policy.compact(expected_projection),'kernel projection contract drift')
        values[bound]=value;endpoints.append('ntruplus/proof/768/ref/kem_runtime_bound/NTRUPlus768RTKernelCosts.ec:'+endpoint)
    return {'status':'KERNEL_SOURCE_FEES_RECONSTRUCTED','endpoints':endpoints,'closed_bounds':values}
