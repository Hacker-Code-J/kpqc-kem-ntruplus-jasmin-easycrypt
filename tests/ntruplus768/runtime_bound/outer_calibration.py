"""Reconstruct complete outer-reducer prices from typed executable bodies.

Metadata is an AST witness, never an authority for erasure, call targets,
array sizes or fees. The recognizer admits only the reviewed outer fragment.
All variable-length callbacks/extraction remain in the separately checked
phase, and only the adversary's own work is symbolic.
"""
import collections
import json
import re

import policy
import calibration_policy as cal
import kernel_calibration as kernel
import manual_calibration as manual
import model_contract
import sim_calibration

PREFIX = 'ntruplus/proof/768/ref/'
GROUP = 'kem_runtime_bound/'
# key: source file, procedure, ghost locals, retained result expression
SPECS = {
 'top_di':('RTWordReduction','RTWord_DI.measure',('profile',),'out.`1'),
 'top_do':('RTWordReduction','RTWord_DO.measure',('profile',),'out.`1'),
 'top_co':('RTWordReduction','RTWord_CO.measure',('profile',),'out.`1'),
 'word_inj':('RTWordKernels','RTWordINJNTRUReduction.run',('scales','units','encodes','calls','profile'),'win'),
 'word_ow':('RTWordKernels','RTWordOWNTRUReduction.run',('scales','units','encodes','profile'),'win'),
 'word_rlwe':('RTWordKernels','RTWordOWRLWESolver.run',('units','encodes','recovers','calls'),'answer'),
 'inj_check':('RTKernels','RTINJCheck.run',('trits','polys','encryptions','ciphers'),'win'),
 'encrypt':('RTKernels','RTEncrypt.run',('calls',),'ct'),
 'ow_kernel':('RTKernels','RTOWKernel.run',('draws','calls','comparisons'),'win'),
 'aux_inj':('../kem_acwc2_security/NTRUPlus768SecBaseGames','SecINJAuxAdapter.run',(),'out'),
 'aux_ow':('../kem_acwc2_security/NTRUPlus768SecBaseGames','SecOWAuxAdapter.run',(),'out'),
 'measured_inj_run':('RTProjection','RTMeasuredINJ.run',(),'out.`1'),
 'measured_inj':('RTProjection','RTMeasuredINJ.measure',('draws',),'collision'),
 'measured_ow':('RTProjection','RTMeasuredOW.run',(),'if out=None then sec_zero else (oget out).`1'),
 'extract_wrapper':('RTProjection','RTExtract.run',(),'out.`1'),
}
FIELDS = ('scale','unit','encode','recover','encrypt','trit','poly_compare','cipher_compare','psi_draw','attacker')
KERNELS = {
 'RTWordScale3.run':('scale','RTWordScale3.measure',1,768,'19204'),
 'RTWordUnit.run':('unit','RTKernelUnit.run',1,0,'rt_kernel_unit_bound'),
 'RTWordEncode.run':('encode','RTKernelEncode.run',1,1152,'rt_kernel_encode_bound'),
 'RTWordRecover.run':('recover','RTKernelRecover.run',3,768,'rt_kernel_recover_bound'),
 'PKEEnc.run':('encrypt','RTKernelPKEEnc.run',3,1152,'rt_kernel_pkeenc_bound'),
 'RRecTrit.check':('trit','RTFixedWordChecks.trit',1,0,'rt_fixed_trit_bound'),
 'RTPolyEqual.run':('poly_compare','RTPrimitive.word_equal',2,0,'rt_word_compare_steps 768'),
 'HistKey.cipher':('cipher_compare','RTPrimitive.cipher',2,0,'rt_byte_compare_steps 1152'),
}
EDGES = {
 ('top_di','RTWordINJNTRUReduction(RTAuxINJ(S,A)).run'):'word_inj',
 ('top_do','RTWordOWNTRUReduction(RTAuxOW(S,A)).run'):'word_ow',
 ('top_co','RTWordOWRLWESolver(RTAuxOW(S,A)).run'):'word_rlwe',
 ('word_inj','B.run'):'aux_inj',('word_inj','RTINJCheck.run'):'inj_check',
 ('word_ow','RTOWKernel(B).run'):'ow_kernel',('word_rlwe','B.run'):'aux_ow',
 ('ow_kernel','RTEncrypt.run'):'encrypt',('ow_kernel','B.run'):'aux_ow',
 ('aux_inj','B.run'):'measured_inj_run',('aux_ow','B.run'):'measured_ow',
 ('measured_inj_run','measure'):'measured_inj',('measured_inj','RTEncrypt.run'):'encrypt',
 ('measured_inj','RTExtract(S).run'):'extract_wrapper',('measured_ow','RTExtract(S).run'):'extract_wrapper',
}
EXTERNAL = {
 ('aux_inj','SecAuxSetup.run'):('setup_phase','setup',0),
 ('aux_ow','SecAuxSetup.run'):('setup_phase','setup',0),
 ('measured_inj','RTTranscript(S,A).run'):('adaptive_phase','phase',0),
 ('measured_ow','RTTranscript(S,A).run'):('adaptive_phase','phase',0),
 ('extract_wrapper','CostExtract.run'):('extraction_phase','extraction',1536),
}
ATTACKER_EDGES = {('word_inj','B.run'),('word_rlwe','B.run'),('ow_kernel','B.run')}
GHOST_CALLS = {'S.reset_cost':'','S.metrics':'','S.charge_extract':'out.`2'}
GHOST_OPS = {'rtk_profile','rtk_add','rt_inj_complete_profile'}
GUARDS = {
 'word_inj':{'accept'},'word_ow':{'accept'},
 'word_rlwe':{'accept','recovered<>None'},
 'inj_check':{'v0/\\v1/\\v2/\\v3/\\!(em/\\er)'},
}
ASSIGNMENTS = {
 ('word_inj','win'):{'false','checked.`1'},
 ('word_ow','win'):{'false','checked.`1'},
 ('word_rlwe','answer'):{'Array768.init(fun_=>W16.zero)','ogetrecovered'},
 ('inj_check','win'):{'false','cmp.`1'},
 ('encrypt','ct'):{'ifout=NonethenArray1152.init(fun_=>W8.zero)elseogetout'},
 ('measured_inj','collision'):{'ifout=Nonethen(code,code,r,r)else(code,(ogetout).`1,r,(ogetout).`2)'},
}



def split_top(text, separator=','):
    result=[];start=0;depth=0
    for i,c in enumerate(text):
        if c=='(':depth+=1
        elif c==')':depth-=1
        policy.require(depth>=0,'unbalanced outer expression')
        if c==separator and depth==0:result.append(text[start:i].strip());start=i+1
    policy.require(depth==0,'unbalanced outer expression')
    result.append(text[start:].strip())
    return result


def unparen(text):
    from fee_checker import closing
    text=text.strip()
    while text.startswith('(') and closing(text,0)==len(text)-1:text=text[1:-1].strip()
    return text


def type_parts(ty):
    aliases={'pke_poly':'W16.t Array768.t',
             'sec_collision':'W16.t Array768.t*W16.t Array768.t*W16.t Array768.t*W16.t Array768.t'}
    ty=unparen(ty)
    if ty in aliases:ty=aliases[ty]
    return split_top(ty,'*')


def cells(ty):
    ty=unparen(ty)
    if ty.endswith(' list') or ty in ('unit','rt_profile','rt_kernel_profile'):return 0
    if ty.endswith(' option'):return cells(ty[:-7])
    parts=type_parts(ty)
    if len(parts)>1:return sum(cells(x) for x in parts)
    if parts[0]!=ty:return cells(parts[0])
    kernel.validate_type(ty)
    return kernel.type_cells(ty)


def signature(text, qualified):
    """Use the common typed extractor after erasing only pointer/ghost types."""
    sanitized=re.sub(r'W8\.t\s+Array1152\.t\s+list','bool',text)
    sanitized=re.sub(r'\bsec_collision\b','(pke_poly*pke_poly*pke_poly*pke_poly)',sanitized)
    sanitized=re.sub(r'\b(?:rt_profile|rt_kernel_profile|unit)\b','bool',sanitized)
    # The original types are retained below for field selection/ghost checks.
    checked_params,_checked_types,checked_ret=kernel.signature(sanitized,qualified)
    module,proc=qualified.split('.')[-2:]
    hits=[(header,body) for m,b in model_contract.syntax.modules(text) if m==module
          for name,header,body,_i,_j in model_contract.syntax.procedures(b) if name==proc]
    policy.require(len(hits)==1,'outer source signature ambiguous')
    header,body=hits[0]
    from fee_checker import closing
    a=header.index('(');b=closing(header,a);params={}
    for group in split_top(header[a+1:b]):
        if not group:continue
        names,ty=group.split(':',1)
        for name in names.split():params[name]=ty.strip()
    ret=header[b+1:].strip().removeprefix(':').strip()
    policy.require(ret.endswith('='),'outer result signature malformed');ret=ret[:-1].strip()
    types=dict(params)
    for match in re.finditer(r'\bvar\s+([^:;]+):([^;]+);',body):
        for name in re.findall(r'\w+',match.group(1)):types[name]=match.group(2).strip()
    for ty in [*types.values(),ret]:cells(ty)
    policy.require(list(checked_params)==list(params),'typed outer parameter drift')
    return params,types,ret


def expression_type(expr, types):
    expr=unparen(expr)
    if expr in ('true','false'):return 'bool'
    if expr.startswith('Some '):return expression_type(expr[5:],types)+' option'
    if expr.startswith('oget '):
        ty=unparen(expression_type(expr[5:],types));policy.require(ty.endswith(' option'),'oget on nonoption')
        return ty[:-7]
    match=re.fullmatch(r'(.+)\.\`([1-9]\d*)',expr)
    if match:
        parts=type_parts(expression_type(match[1],types));index=int(match[2])-1
        policy.require(index<len(parts),'outer selector is out of tuple range')
        return parts[index]
    policy.require(expr in types,'untyped data expression: '+expr)
    return types[expr]


def scalar_ops(expr, types, ghosts=()):
    names=re.findall(r'[A-Za-z_]\w*(?:\.\w+)*',expr)
    policy.require(not(set(names)&set(ghosts)),'ghost value reaches executable expression')
    policy.require(set(names)<=set(types)|{'Some','None','oget','true','false'},'unsupported outer pure operation')
    remaining=re.sub(r'[A-Za-z_]\w*(?:\.\w+)*','',expr)
    remaining=re.sub(r'\.\`\d+','',remaining)
    for token in ('/\\','\\/','<>','!','=','(',')',','):remaining=remaining.replace(token,'')
    policy.require(not re.search(r'[^\s\d]',remaining),'unsupported outer arithmetic/guard')
    return len(re.findall(r'\b(?:Some|oget)\b|\.\`\d+|<>|(?<![<>=])=(?![=>])|/\\|\\/|!',expr))


def ghost_expr(expr, types, ghosts):
    names=set(re.findall(r'[A-Za-z_]\w*',expr))
    policy.require(names<=set(types)|GHOST_OPS,'unsupported ghost expression')
    # No calls, memory operations, control flow or cryptographic operators.
    remaining=re.sub(r'[A-Za-z_]\w*|\.\`\d+|\d+','',expr)
    policy.require(not re.search(r'[^\s()+,]',remaining),'effectful/nonfinite ghost expression')


def numeric(expr, values):
    """Safe parser for the four reviewed prefix helpers and integer sums."""
    tokens=re.findall(r'\d+|[A-Za-z_]\w*|[()+*]',expr)
    policy.require(''.join(tokens)==re.sub(r'\s+','',expr),'unsupported outer bound token')
    pos=0
    helpers={'rt_outer_copy':(1,lambda n:3*n),'rt_outer_frame':(2,lambda a,n:2+a+3*n),
             'rt_outer_zero_steps':(1,lambda n:10*n+5),'rt_outer_zero_call':(1,lambda n:13*n+7),
             'rt_word_compare_steps':(1,lambda n:16*n+5),'rt_byte_compare_steps':(1,lambda n:18*n+5)}
    def atom():
        nonlocal pos
        policy.require(pos<len(tokens),'missing bound atom');t=tokens[pos];pos+=1
        if t=='(':
            v=add();policy.require(pos<len(tokens) and tokens[pos]==')','unclosed bound group');pos+=1;return v
        if t.isdigit():return int(t)
        if t in helpers:
            arity,fn=helpers[t];return fn(*[atom() for _ in range(arity)])
        policy.require(t in values,'unclosed outer cost symbol: '+t);return values[t]
    def mul():
        nonlocal pos
        v=atom()
        while pos<len(tokens) and tokens[pos]=='*':pos+=1;v*=atom()
        return v
    def add():
        nonlocal pos
        v=mul()
        while pos<len(tokens) and tokens[pos]=='+':pos+=1;v+=mul()
        return v
    value=add();policy.require(pos==len(tokens),'trailing outer cost expression');return value


def op_expression(text,name):
    matches=list(re.finditer(r'\bop\s+'+re.escape(name)+r'\b[^=]*=([^.]*)\.',policy.without_comments(text)))
    policy.require(len(matches)==1,'missing/ambiguous outer cost operation: '+name);return matches[0].group(1).strip()


def _call_parts(args, types, result_cells, ghosts):
    args=split_top(args) if args.strip() else []
    selectors=0;constructors=0;payload=0
    for arg in args:
        ops=scalar_ops(arg,types,ghosts)
        if arg.startswith('Some '):constructors+=1;payload+=3*cells(expression_type(arg[5:],types));ops-=1
        selectors+=ops
    return {'call_frame':2,'arguments':len(args),'result_clone':3*result_cells,
            'selectors':selectors,'constructor':constructors,'constructor_payload_clone':payload}


def _check_nodes(key,nodes,types,records,ghosts,result_cells):
    source=[];cost=0;profile=collections.Counter();edges=collections.Counter()
    for n in nodes:
        kind=n['kind'];bucket=n.get('bucket');parts=None
        if kind=='assign':
            lhs,expr=n['lhs'],n['expr'];policy.require(lhs in types,'unknown outer assignment target')
            stmt=lhs+'<-'+expr+';'
            if lhs in ghosts:
                policy.require(bucket=='ghost_erasure' and cells(types[lhs])==0,'data-bearing assignment erased')
                ghost_expr(expr,types,ghosts);fee=0
            else:
                policy.require(bucket=='fixed','ordinary assignment not priced')
                compact=policy.compact(expr)
                policy.require(compact in ASSIGNMENTS.get((key,lhs),set()),'unsupported non-ghost outer assignment')
                if compact=='Array768.init(fun_=>W16.zero)':
                    policy.require(key=='word_rlwe' and lhs=='answer','unexpected zero-word construction')
                    parts={'transfer':1,'zero_lowering':13*768+7}
                    policy.require(n.get('lowering')=='RTOuterZero.words','wrong zero-word lowering')
                elif compact=='ifout=NonethenArray1152.init(fun_=>W8.zero)elseogetout':
                    policy.require(key=='encrypt' and lhs=='ct','unexpected zero-cipher construction')
                    parts={'transfer':1,'guard':2,'branch_max':max(13*1152+7,1+3*1152)}
                    policy.require(n.get('lowering')=='RTOuterZero.cipher','wrong zero-cipher lowering')
                elif compact=='ifout=Nonethen(code,code,r,r)else(code,(ogetout).`1,r,(ogetout).`2)':
                    policy.require(key=='measured_inj' and lhs=='collision','unexpected collision constructor')
                    parts={'guard':2,'tuple_constructor':3,'selectors':4,'transfer':1,'result_clone':3*cells(types[lhs])}
                else:
                    ops=scalar_ops(expr,types,ghosts)
                    parts={'transfer':1,'selectors':ops,'result_clone':3*cells(types[lhs])}
                fee=sum(parts.values())
        elif kind=='sample':
            policy.require(n['law']=='pke_psi1' and n['lhs'] in ('code','r') and key in ('ow_kernel','measured_inj'),'unsupported sampled distribution')
            policy.require(bucket=='kernel_profile' and n['field']=='psi_draw' and n['multiplicity']==1,'sample not in kernel profile')
            policy.require((n['lowering'],n['distribution_equivalence'],n['cost_theorem'])==('RTPsiSampler.measure','rt_psi_sampler_law','rt_outer_psi_call_cost'),'unproved sampling lowering')
            stmt=n['lhs']+'<$pke_psi1;';profile['psi_draw']+=1;fee=0
        elif kind=='call':
            target,args=n['target'],n['args'];lhs=n['lhs'];edge=(key,target)
            stmt=(lhs+'<@' if lhs else '')+target+'('+args+');'
            if target in GHOST_CALLS:
                policy.require(target=='S.charge_extract' and key=='extract_wrapper' or target!='S.charge_extract' and key.startswith('top_'),'ghost-call scope changed')
                policy.require(bucket=='ghost_erasure' and policy.compact(args)==policy.compact(GHOST_CALLS[target]),'data call erased as ghost')
                if target=='S.metrics':policy.require(lhs in ghosts,'metrics escapes ghost state')
                fee=0
            elif target in KERNELS:
                field,_measured,arity,_cells,_bound=KERNELS[target]
                policy.require(bucket=='kernel_profile' and (n['field'],n['multiplicity'])==(field,1),'kernel bucket substituted')
                argv=split_top(args);policy.require(len(argv)==arity,'kernel arity changed')
                fee=sum(scalar_ops(x,types,ghosts) for x in argv)
                policy.require(n['selector_fee']==fee,'kernel argument selector undercharge');profile[field]+=1
            else:
                if edge in EDGES:
                    child=EDGES[edge];policy.require(bucket=='fixed_callee' and n['callee_key']==child,'wrong concrete callee edge')
                    c=records[child];ret=c['_return_cells'];arity=len(c['_params']);edges[child]+=1
                    if edge in ATTACKER_EDGES:
                        policy.require(n.get('attacker_profile_increment')==1,'actual B invocation not counted');profile['attacker']+=1
                    else:policy.require(not n.get('attacker_profile_increment'),'spurious attacker invocation')
                else:
                    policy.require(edge in EXTERNAL,'unclosed source call: '+str(edge));b,child,ret=EXTERNAL[edge]
                    policy.require(bucket==b and n['callee_key']==child,'phase/outer bucket drift')
                    arity={'setup':1,'phase':2,'extraction':4}[child]
                policy.require(n['return_cells']==ret,'callee result-copy size drift')
                parts=_call_parts(args,types,ret,ghosts)
                policy.require(parts['arguments']==arity,'concrete/phase call arity changed');fee=sum(parts.values())
        elif kind=='if':
            policy.require(bucket=='fixed','branch erased or put in unknown bucket')
            policy.require(policy.compact(n['cond']) in GUARDS.get(key,set()),'unreviewed outer guard complexity/type')
            ops=scalar_ops(n['cond'],types,ghosts);guard=1+ops
            body,inner,pro,edg=_check_nodes(key,n['body'],types,records,ghosts,result_cells)
            # This source fragment uses only an optional then body. Reject a
            # metadata else omission instead of silently ignoring it.
            policy.require(not n.get('else'),'outer else branch requires a new checked rule')
            fee=guard+inner;stmt='if('+n['cond']+'){'+body+'}'
            policy.require(n['guard_fee']==guard and n['branch_bound']==inner,'branch local bound drift')
            profile+=pro;edges+=edg
        elif kind=='match':
            policy.require(bucket=='fixed','option match unpriced');scalar_ops(n['expr'],types,ghosts)
            ty=unparen(expression_type(n['expr'],types));policy.require(ty.endswith(' option'),'match on non-option')
            payload=cells(ty[:-7]);branches=[];maxcost=0;maxp=collections.Counter();maxe=collections.Counter()
            policy.require(len(n['branches'])==2 and n['branches'][0]['pattern']=='None','option branch coverage incomplete')
            for branch in n['branches']:
                pattern=branch['pattern'];local=dict(types)
                if pattern=='None':clone=0
                else:
                    m=re.fullmatch(r'Some (\w+)',pattern);policy.require(m,'unsupported option pattern');local[m[1]]=ty[:-7];clone=3*payload
                code,inner,pro,edg=_check_nodes(key,branch['body'],local,records,ghosts,result_cells)
                policy.require(branch['binding_clone']==clone and branch['body_bound']==inner,'Some payload/branch cost omitted')
                maxcost=max(maxcost,clone+inner)
                for k,v in pro.items():maxp[k]=max(maxp[k],v)
                for k,v in edg.items():maxe[k]=max(maxe[k],v)
                branches.append('|'+pattern+'=>{'+code+'}')
            fee=2+maxcost;stmt='match '+n['expr']+' with'+''.join(branches)+'end;'
            policy.require(n['tag_and_branch']==2 and n['branch_max']==maxcost,'option test/branch price drift')
            profile+=maxp;edges+=maxe
        elif kind=='return':
            expr=n['expr'];data=SPECS[key][3]
            if key=='measured_ow':
                policy.require(policy.compact(expr)==policy.compact(data) and n.get('lowering')=='RTOuterZero.words','OW zero fallback drift')
                parts={'return':1,'result_clone':3*result_cells,'guard':2,'branch_max':max(13*768+7,2)}
                policy.require(n['false_branch_selectors']==2,'OW fallback selector drift')
            else:
                if key in ('aux_inj','aux_ow','measured_inj_run','extract_wrapper'):
                    policy.require(policy.compact(expr)==policy.compact(data),'outer returned data drift')
                else:
                    values=split_top(unparen(expr));policy.require(len(values)>=2 and policy.compact(values[0])==policy.compact(data),'certificate erasure changes returned data')
                    for ghost in values[1:]:ghost_expr(ghost,types,ghosts)
                ops=scalar_ops(data,types,ghosts)
                parts={'return':1,'result_clone':3*result_cells,'selectors':ops}
            policy.require(n.get('data_expression',data)==data,'metadata retained result differs')
            fee=sum(parts.values());stmt='return '+expr+';'
        else:raise ValueError('unsupported outer statement: '+kind)
        if parts is not None:policy.require(n.get('fee_parts')==parts,'outer primitive decomposition differs: '+key+':'+kind)
        policy.require(n['local_fee']==fee,'outer instruction fee differs: '+key+':'+kind)
        policy.require(policy.compact(n['source_statement'])==policy.compact(stmt),'outer AST witness differs from statement')
        source.append(stmt);cost+=fee
    return ''.join(source),cost,profile,edges


def _zeros(data,text):
    policy.require({x['procedure'] for x in data['zero_lowerings']}=={'RTOuterZero.words','RTOuterZero.cipher'},'zero lowering omitted')
    endpoints=[]
    for z in data['zero_lowerings']:
        word=z['procedure'].endswith('words');n=768 if word else 1152;zero='W16.zero' if word else 'W8.zero'
        init={'scratch_alloc_and_transfer':n+1,'index_init':1,'loop_guard':2}
        loop={'zero_element_store_and_transfer':2,'index_increment':2,'loop_guard':2}
        ret={'return':1,'result_clone':3*n};total=sum(init.values())+n*sum(loop.values())+sum(ret.values())
        policy.require(z['cells']==n and z['initial_parts']==init and z['loop_parts']==loop and z['return_parts']==ret,'zero source-price decomposition drift')
        policy.require((z['initial_cost'],z['iteration_cost'],z['return_cost'],z['cost_result'],z['call_with_binding'])==(n+4,6,3*n+1,total,total+2+3*n),'zero bound arithmetic drift')
        expected=f'out<-witness;work<-{n+1};i<-0;work<-work+1;work<-work+2;while(i<{n}){{out.[i]<-{zero};work<-work+2;i<-i+1;work<-work+2;work<-work+2;}}work<-work+{3*n+1};return(out,work);'
        policy.require(manual.normalize(cal.raw_body(text,z['procedure']))==policy.compact(expected),'zero actual loop/charge drift')
        theorem='rt_outer_zero_'+('words' if word else 'cipher')+'_correct'
        value='sec_zero' if word else 'Array1152.init(fun _=>W8.zero)'
        expected_lemma=f'lemma {theorem}:phoare[{z["procedure"]}:true ==>res=({value},rt_outer_zero_steps {n})]=1%r.'
        policy.require(cal.lemma_declaration(text,theorem)==policy.compact(expected_lemma),'zero functional/cost contract drift')
        endpoints.append(data['file']+':'+z['procedure'])
    return endpoints


def _dispatchers(data,values,require_complete):
    rows=data.get('run_dispatchers',[])
    expected={'RTWord_'+x+'.run' for x in ('DI','DO','CO')}
    policy.require(len(rows)==3 and {r['source_proc'] for r in rows}==expected,'actual run dispatcher coverage incomplete')
    source=policy.PROOF/'NTRUPlus768RTWordReduction.ec';text=source.read_text()
    complete=policy.PROOF/'NTRUPlus768RTCompleteCost.ec'
    policy.require(complete.is_file() or not require_complete,'complete actual-run cost composition pending')
    complete_text=complete.read_text() if complete.is_file() else ''
    endpoints=[];closed={}
    for r in rows:
        qualified=r['source_proc'];label=qualified.split('.')[0].removeprefix('RTWord_').lower()
        policy.require(r['file']==GROUP+'NTRUPlus768RTWordReduction.ec' and r['source_sha256']==policy.sha(source.read_bytes()),'dispatcher source substituted')
        params,types,ret=signature(text,qualified);inc=sum(cells(t) for t in params.values());out=cells(ret)
        args=','.join(params);body=cal.raw_body(text,qualified)
        policy.require(manual.normalize(body)==policy.compact('out<@measure('+args+');return out.`1;'),'actual dispatcher must execute its measure exactly once')
        policy.require(policy.compact(r['body'])==policy.compact(body) and r['source_body_sha256']==policy.sha(policy.compact(body).encode()),'dispatcher metadata omits actual body')
        parts={'entry_clone':3*inc,'call_frame':2,'arguments':len(params),
               'call_result_clone':3*out,'return':1,'result_selector':1,'return_clone':3*out}
        total=sum(parts.values());op='rt_run_'+label+'_overhead'
        policy.require((r['input_cells'],r['result_cells'],r['arity'],r['measure_call_count'])==(inc,out,len(params),1),'dispatcher signature/multiplicity drift')
        policy.require(r['measure_target']==qualified.removesuffix('run')+'measure','dispatcher does not match priced core')
        policy.require(r['fee_parts']==parts and r['cost']==total and r['complete_cost_op']==op,'dispatcher boundary undercharged')
        policy.require(r.get('kernel_or_phase_duplicate') is False,'dispatcher was hidden in a different price bucket')
        if complete_text:policy.require(numeric(op_expression(complete_text,op),values)==total,'complete-cost dispatcher price differs from actual source')
        closed[op]=total;endpoints.append(PREFIX+r['file']+':'+qualified)
    if complete_text:
        # Order in the source lemma is DI, DO, CO, independently of JSON order.
        declaration='lemma rt_run_dispatcher_values : '+ ' /\\ '.join('rt_run_'+x+'_overhead='+str(closed['rt_run_'+x+'_overhead']) for x in ('di','do','co'))+'.'
        policy.require(cal.lemma_declaration(complete_text,'rt_run_dispatcher_values')==policy.compact(declaration),'dispatcher value theorem does not certify the actual three sources')
    return endpoints,closed


def _check_record(data,require_complete):
    policy.require(data['schema']=='rt-outer-source-calibration-v1','unknown outer calibration schema')
    policy.require(data['file']==PREFIX+GROUP+'NTRUPlus768RTOuterCost.ec','outer pricing source substituted')
    text=cal.path(data['file']).read_text()
    policy.require(policy.sha(text.encode())==data['source_sha256'],'outer price file pin drift')
    helpers={'rt_outer_copy':'op rt_outer_copy(n:int)=3*n.',
             'rt_outer_frame':'op rt_outer_frame(arity cells:int)=2+arity+rt_outer_copy cells.',
             'rt_outer_zero_steps':'op rt_outer_zero_steps(n:int)=10*n+5.',
             'rt_outer_zero_call':'op rt_outer_zero_call(n:int)=rt_outer_zero_steps n+rt_outer_frame 0 n.'}
    for name,expected in helpers.items():
        decls=re.findall(r'\bop\s+'+re.escape(name)+r'\b[^=]*=[^.]*\.',policy.without_comments(text))
        policy.require(len(decls)==1 and policy.compact(decls[0])==policy.compact(expected),'outer primitive helper redefined')
        policy.require(data['helper_definitions'][name]==expected,'outer helper metadata differs')
    manual.check(require_complete);values=dict(sim_calibration.check(require_complete)['closed_bounds'])
    endpoints=_zeros(data,text)
    # These manual endpoints are independently checked above. Recompute the
    # scalar ceilings from their fixed loops rather than trust metadata fees.
    prices={
     'scale':3*768+1+2+768*(4+2+2+2+2+3+2+2)+3*768+1+2+1+3*768,
     'unit':values['rt_kernel_unit_bound']+3,
     'encode':values['rt_kernel_encode_bound']+3+3*1152,
     'recover':values['rt_kernel_recover_bound']+5+3*768,
     'encrypt':values['rt_kernel_pkeenc_bound']+5+3*1152,
     'trit':values['rt_fixed_trit_bound']+3,
     'poly_compare':16*768+5+4,'cipher_compare':18*1152+5+4,
     'psi_draw':values['rt_fixed_cbd_bound']+385+192+769+2308+2305+2+3*768}
    policy.require(data['kernel_prices']==prices and tuple(data['kernel_profile_order'])==FIELDS,'outer kernel prices are not closed callees')
    # The actual EC price constructor must use these nine closed body prices
    # and precisely tA as its last component, not an arbitrary B/runtime fee.
    price_expr=op_expression(text,'rt_concrete_kernel_prices')
    policy.require(price_expr.startswith('rtk_profile'),'outer price constructor changed')
    remaining=price_expr[len('rtk_profile'):].strip();terms=[]
    from fee_checker import closing
    while remaining:
        if remaining[0]=='(':
            end=closing(remaining,0);terms.append(remaining[1:end]);remaining=remaining[end+1:].strip()
        else:
            m=re.match(r'[A-Za-z_]\w*|\d+',remaining);policy.require(m,'malformed profile price term')
            terms.append(m.group());remaining=remaining[m.end():].strip()
    policy.require(len(terms)==10 and terms[-1]=='tA','attacker self-price erased or changed')
    for field,term in zip(FIELDS[:-1],terms[:-1]):
        policy.require(numeric(term,values)==prices[field],'actual EC kernel price not source-derived: '+field)
    projection=(policy.PROOF/'NTRUPlus768RTProjection.ec').read_text()
    for alias in (
      'module RTAuxINJ(S:RTHistory,A:CCAExtendedAdversary)=SecINJAuxAdapter(RTMeasuredINJ(S,A)).',
      'module RTAuxOW(S:RTHistory,A:CCAExtendedAdversary)=SecOWAuxAdapter(RTMeasuredOW(S,A)).'):
        policy.require(policy.compact(alias) in policy.compact(policy.without_comments(projection)),'actual outer functor binding changed')

    sampler=(policy.PROOF/'NTRUPlus768RTPsiSampler.ec').read_text()
    for name,statement in {
      'rt_psi_sampler_law':'lemma rt_psi_sampler_law:equiv[RTPsiSampler.run~RTPsiLaw.run:true ==> ={res}].',
      'rt_psi_sampler_measure_projection':'lemma rt_psi_sampler_measure_projection:equiv[RTPsiSampler.measure~RTPsiSampler.run:true ==>res{1}.`1=res{2}].',
      'rt_uniform192_byte_product':'lemma rt_uniform192_byte_product:uniform192=dmap(dlist W8.dword 192)(Array192.of_list W8.zero).'
    }.items():policy.require(cal.lemma_declaration(sampler,name)==policy.compact(statement),'unproved fixed sampling implementation')
    policy.require(set(data['kernel_callees'])==set(FIELDS[:-1]),'kernel price coverage incomplete')
    psi=data['kernel_callees']['psi_draw']
    policy.require(psi=={'actual':'pke_psi1 distribution','measured':'RTPsiSampler.measure',
      'body_bound':'rt_fixed_cbd_bound+5767+192','arity':0,'result_cells':768,
      'cost_theorem':'rt_outer_psi_call_cost','distribution_equivalence':'rt_psi_sampler_law',
      'projection':'rt_psi_sampler_measure_projection'},'sampling certificate metadata substituted')
    projections={'scale':'rt_word_scale3_measure_projection','unit':'rt_kernel_unit_projection',
      'encode':'rt_kernel_encode_projection','recover':'rt_kernel_recover_projection',
      'encrypt':'rt_kernel_pkeenc_projection','trit':'rt_fixed_trit_projection',
      'poly_compare':'rt_outer_poly_compare_projection','cipher_compare':'rt_primitive_cipher_projection'}

    for actual,(field,measured,arity,n,bound) in KERNELS.items():
        c=data['kernel_callees'][field]
        policy.require((c['actual'],c['measured'],c['arity'],c['result_cells'],c['body_bound'])==(actual,measured,arity,n,bound),'kernel substitution/arity drift')
        policy.require(c['projection']==projections[field] and c['cost_theorem']=='rt_outer_'+field+'_call_cost','kernel value/cost theorem substituted')
        contract=f'lemma rt_outer_{field if field not in ("poly_compare","cipher_compare") else field}_call_cost:hoare[{measured}:true ==>0<=res.`2+rt_outer_frame {arity} {n}<=(rt_concrete_kernel_prices 0).`rtk_{field}].'
        policy.require(cal.lemma_declaration(text,'rt_outer_'+field+'_call_cost')==policy.compact(contract),'actual kernel cost contract drift')
    records={r['key']:r for r in data['procedures']}
    policy.require(set(records)==set(SPECS) and len(records)==len(data['procedures']),'outer procedure inventory drift')
    for key,r in records.items():
        file,qualified,ghosts,_ret=SPECS[key]
        relative=(GROUP+'NTRUPlus768'+file+'.ec') if not file.startswith('../') else file[3:]+'.ec'
        policy.require(r['file']==relative and r['source_proc']==qualified,'outer source endpoint substituted')
        source=(policy.BASE/relative).read_text()
        policy.require(policy.sha(source.encode())==r['source_sha256'],'outer original source pin drift')
        params,types,ret=signature(source,qualified)
        inc=sum(cells(t) for t in params.values());out=cells(ret)
        policy.require((r['input_cells'],r['return_cells'],r['entry_fee'])==(inc,out,3*inc),'outer input/result type omitted')
        policy.require(tuple(r['ghost_variables'])==ghosts,'unreviewed ghost-erasure variable')
        r['_params']=params;r['_types']=types;r['_return_cells']=out;r['_source']=source
    calculated={};profiles={};edges={}
    for key,r in records.items():
        code,local,pro,edg=_check_nodes(key,r['body_nodes'],r['_types'],records,SPECS[key][2],r['_return_cells'])
        source_body=cal.raw_body(r['_source'],r['source_proc'])
        policy.require(manual.normalize(source_body)==policy.compact(code),'outer original executable statement omitted: '+key)
        policy.require(policy.compact(r['body'])==policy.compact(source_body) and policy.sha(policy.compact(source_body).encode())==r['source_body_sha256'],'outer source-body pin drift')
        total=3*sum(cells(t) for t in r['_params'].values())+local
        policy.require(total==r['fixed_subtotal'],'outer fixed subtotal undercharged: '+key)
        policy.require([pro[f] for f in FIELDS]==r['direct_kernel_profile'],'outer kernel call multiplicity drift: '+key)
        policy.require(sorted(edg.elements())==sorted(r['fixed_callee_edges']),'outer fixed call edge omitted')
        expr=op_expression(text,r['bound_op']);policy.require(policy.compact(expr)==policy.compact(r['bound_expression']),'outer source bound expression drift')
        policy.require(numeric(expr,values)==total,'outer EC subtotal differs from source fee: '+key)
        calculated[key]=total;profiles[key]=pro;edges[key]=edg;values[r['bound_op']]=total
        endpoints.append(PREFIX+r['file']+':'+r['source_proc'])
    def expand(key,stack=()):
        policy.require(key not in stack,'recursive outer call graph has no bound')
        visits=collections.Counter({key:1});pro=profiles[key].copy()
        for child,n in edges[key].items():
            cv,cp=expand(child,stack+(key,))
            for k,v in cv.items():visits[k]+=n*v
            for k,v in cp.items():pro[k]+=n*v
        return visits,pro
    closed={};caps={'di':[1,1,1,0,3,4,2,1,2,1],'do':[1,1,1,0,1,0,1,0,2,1],'co':[0,1,2,1,0,0,0,0,0,1]}
    reduction=(policy.PROOF/'NTRUPlus768RTReduction.ec').read_text()
    for label,cap in caps.items():
        visits,pro=expand('top_'+label);record=data['endpoints'][label]
        policy.require(all(v==1 for v in visits.values()),'outer fixed helper now executes more than once')
        policy.require(set(record['fixed_blocks'])==set(visits) and len(record['fixed_blocks'])==len(visits),'outer endpoint fixed closure omitted')
        policy.require([pro[f] for f in FIELDS]==cap==record['profile_cap'],'actual outer kernel/attacker closure changed')
        decl='rtk_profile '+' '.join(map(str,cap))
        policy.require(policy.compact(op_expression(reduction,'rt_'+label+'_kernel_bound'))==policy.compact(decl),'actual returned profile bound changed')
        fixed=sum(calculated[k]*v for k,v in visits.items());kernel_total=sum(prices[f]*cap[i] for i,f in enumerate(FIELDS[:-1]));total=fixed+kernel_total
        policy.require((record['fixed_total'],record['kernel_total_without_tA'],record['bound_without_tA'])==(fixed,kernel_total,total),'complete outer price arithmetic drift')
        policy.require(numeric(op_expression(text,'rt_outer_'+label+'_fixed'),values)==fixed,'actual final outer fixed sum drift')
        policy.require(record['actual_endpoint']=='RTWord_'+label.upper()+'(S,A).measure','cost endpoint not actual word reducer')
        closed['rt_outer_'+label+'_fixed']=fixed;closed['rt_outer_'+label+'_without_tA']=total
        charge='rt_outer_'+label+'_fixed+rtk_charge(rt_concrete_kernel_prices tA)k'
        bound='rt_outer_'+label+'_charge tA rt_'+label+'_kernel_bound'
        policy.require(policy.compact(op_expression(text,'rt_outer_'+label+'_charge'))==policy.compact(charge),'whole outer charge drops source costs')
        policy.require(policy.compact(op_expression(text,'rt_outer_'+label+'_bound'))==policy.compact(bound),'whole outer bound uses different profile')
    values_statement='lemma rt_outer_bound_values tA : '+ ' /\\ '.join(
        'rt_outer_'+label+'_bound tA=tA+'+str(closed['rt_outer_'+label+'_without_tA']) for label in ('di','do','co'))+'.'
    policy.require(cal.lemma_declaration(text,'rt_outer_bound_values')==policy.compact(values_statement),'closed outer values theorem differs')

    dispatch_endpoints,dispatch_values=_dispatchers(data,values,require_complete)
    endpoints.extend(dispatch_endpoints);closed.update(dispatch_values)
    return {'status':'OUTER_SOURCE_FEES_RECONSTRUCTED','endpoints':endpoints,'closed_bounds':{**values,**closed},
            'kernel_prices':prices,'actual_word_endpoints':dispatch_endpoints,
            'measured_word_endpoints':[PREFIX+GROUP+'NTRUPlus768RTWordReduction.ec:RTWord_'+x+'.measure' for x in ('DI','DO','CO')],
            'attacker_self':'only t_A, one actual invocation; no whole-reduction time premise',
            'phase_buckets':['setup_phase','adaptive_phase','extraction_phase'],
            'scope':'actual run includes the independently priced dispatcher plus its measured core exactly once',
            'source_calibration':'typed source + complete AST + independently computed fees and recursive callgraph'}


def check(require_complete=True):
    path=policy.TEST/'calibration/manual-outer.json'
    if not path.is_file():
        policy.require(not require_complete,'outer source calibration pending')
        return {'status':'PENDING','endpoints':[],'closed_bounds':{}}
    return _check_record(json.loads(path.read_text()),require_complete)
