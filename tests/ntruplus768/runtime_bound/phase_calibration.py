"""Independent, fail-closed source calibration for the adaptive phase.

The JSON is an assertion to check, never the source of prices, types, call
coverage, or executable semantics.  Scalar lexical work is conservatively
charged in addition to owned array copies.  Persistent lists share tails;
ideal ROM operations and erased ledger observations are explicit boundaries.
"""
import json
import re
from collections import Counter
from pathlib import Path

import policy
import calibration_policy as cal
import kernel_calibration as kernel
import manual_calibration as manual
import model_contract
from fee_checker import closing

# Reviewed endpoint inventory, derived from the actual adaptive execution path.
_GROUPS = {
 'kem_history_refinement/NTRUPlus768HistTable.ec': ('HistKeep.run','HistReverse.run','HistTable.put'),
 'kem_history_refinement/NTRUPlus768HistLookup.ec': ('HistCipherOption.equal','HistLookup.check','HistLookup.run','op.hist_lookup_default'),
 'kem_acwc2_security/NTRUPlus768SecExtract.ec': ('SecExtract.run',),
 'kem_reduction_cost/NTRUPlus768CostExtract.ec': ('CostExtract.run',),
 'kem_adaptive_history/NTRUPlus768AHAdapter.ec': ('AHPublicG.get','AHRecordH.get','AHOracles.raw','AHDecap.decap','AHWrapper.guess'),
 'kem_adaptive_history/NTRUPlus768AHFinal.ec': ('AHPrivateStore.init','AHPrivateStore.snapshot','AHPrivateStore.record'),
 'kem_modified_fo/NTRUPlus768FOGAdapters.ec': ('FOGRawStreams.e','FOGRawStreams.f','FOGRawStreams.g','FOGRawStreams.h','FOGRawStreams.untyped','FOGRaw.full','FOGRaw.get','FOGHash.shake'),
 'kem_acwc2_security/NTRUPlus768SecGOracles.ec': ('SecGLogged.get',),
 'kem_fo_simulation/NTRUPlus768SimOracles.ec': ('SimOracles.g',),
 'kem_adaptive_history/NTRUPlus768AHActualReduction.ec': ('AHActualPhase.run','AHActualTranscript.run','AHActualINJReducer.run','AHActualOWReducer.run'),
 'kem_acwc2_security/NTRUPlus768SecBaseGames.ec': ('SecAuxSetup.run','SecINJAuxAdapter.run','SecOWAuxAdapter.run'),
 'kem_indcca_game/NTRUPlus768CCAQueryCodec.ec': ('op.decode_typed',),
 'kem_indcca_game/NTRUPlus768RawXOFSampling.ec': ('op.raw_xof_output','op.raw_join192'),
 'kem_rom_oracle/NTRUPlus768ROMDomains.ec': ('op.peel1153','op.peel_h'),
 'kem_history_refinement/NTRUPlus768HistModel.ec': ('op.hist_zero_value',),
 'kem_rom_bridge/NTRUPlus768KEMPayloadSpec.ec': ('op.payload_shared_key',),
 'kem_numerical_dfr/NTRUPlus768HashPayloadSampling.ec': ('op.hash_join',),
 'kem_indcca_game/NTRUPlus768CCAOraclePorts.ec': ('SharedCCAOracles.e','SharedCCAOracles.f'),
 'kem_acwc2_security/NTRUPlus768SecExtractModel.ec': ('op.sec_zero',),
 'kem_runtime_bound/NTRUPlus768RTStore.ec': ('RTStoreOps.init','RTStoreOps.record'),
 'kem_runtime_bound/NTRUPlus768RTFinal.ec': ('RTPrivateStore.init','RTPrivateStore.snapshot','RTPrivateStore.record'),
 'kem_modified_fo/NTRUPlus768FOProcedures.ec': ('FOHashG.run',),
 'acwc2_contracts/NTRUPlus768ACWC2HashG.ec': ('ACWC2GPrepare.run',),
 'acwc2_contracts/NTRUPlus768SOTPContracts.ec': ('SOTPEncode.run',),
 'kem_fo_simulation/NTRUPlus768SimLookup.ec': ('SimEncrypt.run',),
}
PREFIX = 'ntruplus/proof/768/ref/'
INVENTORY = {endpoint:PREFIX+file for file,endpoints in _GROUPS.items() for endpoint in endpoints}
WRAPPERS = {'FOHashG.run':'rt_phase_fohash_boundary','ACWC2GPrepare.run':'rt_phase_gprepare_boundary',
            'FOGHash.shake':'rt_phase_foghash_boundary','SOTPEncode.run':'rt_phase_sotp_boundary'}
LOOPS = {'HistKeep.run':'todo<>[]','HistReverse.run':'todo<>[]',
 'HistLookup.run':'todo<>[]/\\answer=None','SecExtract.run':'todo<>[]/\\answer=None',
 'CostExtract.run':'todo<>[]/\\answer=None'}
CALLS = {
 'HistKeep.run':('HistKey.equal',), 'HistReverse.run':(),
 'HistTable.put':('HistKeep.run','HistReverse.run'), 'HistCipherOption.equal':('HistKey.cipher',),
 'HistLookup.check':('HistKey.suffix','SimEncrypt(G).run','HistCipherOption.equal'),
 'HistLookup.run':('HistCipherOption.equal','check'), 'SecExtract.run':('SecCandidate.run',),
 'CostExtract.run':('SecCandidate.run',), 'AHPublicG.get':('O.g',),
 'AHRecordH.get':('O.h','S.record'), 'AHOracles.raw':('O.raw','O.raw','O.raw','O.raw','AHRecordH(S,O).get','O.raw'),
 'AHDecap.decap':('S.snapshot','HistLookup(AHPublicG(O)).run'),
 'AHWrapper.guess':('O.f','S.init','A(AHOracles(S,O),AHDecap(S,O)).guess'),
 'AHPrivateStore.init':(), 'AHPrivateStore.snapshot':(), 'AHPrivateStore.record':('HistTable.put',),
 'FOGRawStreams.e':('ROE.get',), 'FOGRawStreams.f':('ROF.get',), 'FOGRawStreams.g':('G.get',),
 'FOGRawStreams.h':('ROH.get',), 'FOGRawStreams.untyped':(),
 'FOGRaw.full':('FOGRawStreams(G).untyped','FOGRawStreams(G).e','FOGRawStreams(G).f','FOGRawStreams(G).g','FOGRawStreams(G).h'),
 'FOGRaw.get':('full',), 'SecGLogged.get':('G.get',), 'SimOracles.g':('G.get',),
 'AHActualPhase.run':('ROF.get','AHWrapper(S,A,AHActualOracles(G),AHRejectD).guess'),
 'AHActualTranscript.run':('SecGHistory.init','AHActualPhase(S,A,SecGLogged(FOGActual)).run'),
 'SecAuxSetup.run':('ROMInit.init','RawXOFStreams.init','ROF.get'),
 'AHActualINJReducer.run':('AHActualTranscript(S,A).run','SecExtract.run'),
 'AHActualOWReducer.run':('AHActualTranscript(S,A).run','SecExtract.run'),
 'SecINJAuxAdapter.run':('SecAuxSetup.run','B.run'), 'SecOWAuxAdapter.run':('SecAuxSetup.run','B.run'),
 'SharedCCAOracles.e':('ROE.get',), 'SharedCCAOracles.f':('ROF.get',),
 'RTStoreOps.init':(), 'RTStoreOps.record':('HistTable.put',),
 'RTPrivateStore.init':('RTStoreOps.init',), 'RTPrivateStore.snapshot':(), 'RTPrivateStore.record':('RTStoreOps.record',),
 'FOHashG.run':('ACWC2GPrepare.run','G.shake'),
 'ACWC2GPrepare.run':('NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt','NTRUPlus768DecapMessagePrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare'),
 'FOGHash.shake':('G.get',),
 'SOTPEncode.run':('NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode',),
 'SimEncrypt.run':('NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1','FOHashG(FOGHash(G)).run','SOTPEncode.run','PKEEnc.run'),
}
# These definitions are structurally checked before their type/cost rules apply.
OPS = {
 'decode_typed': '''op decode_typed (s:W8.t list):typed_query option =
 if size s=32 then Some(E(Array32.of_list W8.zero s)) else
 if size s=1153 /\\ nth W8.zero s 0=W8.zero then Some(F(peel1153(Array1153.of_list W8.zero s))) else
 if size s=1153 /\\ nth W8.zero s 0=W8.one then Some(G(peel1153(Array1153.of_list W8.zero s))) else
 if size s=129 /\\ nth W8.zero s 0=W8.of_int 2 then Some(H(peel_h(Array129.of_list W8.zero s))) else None.''',
 'raw_xof_output':'op raw_xof_output (n:int)(s:W8.t Array224.t)=take n(Array224.to_list s).',
 'raw_join192':'op raw_join192(p:W8.t Array192.t*W8.t Array32.t):W8.t Array224.t=Array224.init(fun i=>if i<192 then p.`1.[i] else p.`2.[i-192]).',
 'peel1153':'op peel1153(input:W8.t Array1153.t):W8.t Array1152.t=Array1152.init(fun i=>input.[i+1]).',
 'peel_h':'op peel_h(input:W8.t Array129.t):W8.t Array96.t*W8.t Array32.t=(Array96.init(fun i=>input.[i+1]),Array32.init(fun i=>input.[i+97])).',
 'hist_zero_value':'op [opaque] hist_zero_value:W8.t Array224.t=Array224.init(fun _=>W8.zero).',
 'hist_lookup_default':'op [opaque] hist_lookup_default:hist_entry=((Array96.init(fun _=>W8.zero),Array32.init(fun _=>W8.zero)),hist_zero_value).',
 'payload_shared_key':'op [opaque] payload_shared_key(hout:W8.t Array224.t)=Array32.init(fun i=>hout.[i]).',
 'hash_join':'op hash_join(p:W8.t Array32.t*W8.t Array192.t):W8.t Array224.t=Array224.init(fun i=>if i<32 then p.`1.[i] else p.`2.[i-32]).',
 'sec_zero':'op sec_zero:pke_poly=Array768.init(fun _=>W16.zero).',
}
ALIASES = {
 'pke_poly':('pke_average_correctness/NTRUPlus768PKEModel.ec','W16.t Array768.t'),
 'fo_h_input':('kem_modified_fo/NTRUPlus768FOModel.ec','W8.t Array96.t*W8.t Array32.t'),
 'hist_entry':('kem_history_refinement/NTRUPlus768HistModel.ec','fo_h_input*W8.t Array224.t'),
 'hist_table':('kem_history_refinement/NTRUPlus768HistModel.ec','hist_entry list'),
 'cca_reply':('kem_indcca_game/NTRUPlus768CCAStatusAdapter.ec','W8.t Array32.t option'),
 'sec_collision':('kem_acwc2_security/NTRUPlus768SecModel.ec','pke_poly*pke_poly*pke_poly*pke_poly'),
 'ah_state':('kem_adaptive_history/NTRUPlus768AHState.ec','{ah_rows:hist_table;ah_pk:W8.t Array1152.t;ah_suffix:W8.t Array32.t;ah_cstar:W8.t Array1152.t option;}'),
 'typed_query':('kem_rom_oracle/NTRUPlus768ROMDomains.ec','[E of W8.t Array32.t|F of W8.t Array1152.t|G of W8.t Array1152.t|H of (W8.t Array96.t*W8.t Array32.t)]'),
}

ALIASES['rt_profile']=('kem_runtime_bound/NTRUPlus768RTModel.ec','{'+''.join(x+':int;' for x in ('rp_h','rp_size','rp_d','rp_g','rp_q','rp_b','rp_put_v','rp_put_c','rp_dec_v','rp_dec_c','rp_enc','rp_alloc','rp_xcalls','rp_xvisits'))+'}')


def declaration(text,kind,name):
    code=policy.without_comments(text)
    found=re.findall(r'(?ms)^\s*'+kind+r'\s+(?:\[[^]]*\]\s*)?'+re.escape(name)+r'\b.*?(?<!\.)\.\s*(?=\n|$)',code)
    policy.require(len(found)==1,'missing/ambiguous phase declaration: '+name)
    return found[0].strip()


def split_top(text,separator):
    depth=0;start=0;result=[]
    for i,c in enumerate(text):
        if c in '([{':depth+=1
        elif c in ')]}':depth-=1
        policy.require(depth>=0,'unbalanced phase type')
        if c==separator and depth==0:result.append(text[start:i]);start=i+1
    policy.require(depth==0,'unbalanced phase type')
    result.append(text[start:]);return result


def type_cells(ty):
    t=ty.strip()
    policy.require('->' not in t and '=>' not in t,'functional type has no constant-time phase rule')
    while t.startswith('(') and closing(t,0)==len(t)-1:t=t[1:-1].strip()
    parts=split_top(t,'*')
    if len(parts)>1:return sum(type_cells(x) for x in parts)
    if t.endswith(' list'):
        type_cells(t[:-5]);return 0
    if t.endswith(' option'):return type_cells(t[:-7])
    if t in ('int','bool','unit','rt_profile'):return 0
    if t in ALIASES:
        definition=ALIASES[t][1]
        if t=='ah_state':return sum(type_cells(field.split(':',1)[1]) for field in definition[1:-1].split(';') if field)
        if t=='typed_query':return max(type_cells(branch.split(' of ',1)[1]) for branch in definition[1:-1].split('|'))
        return type_cells(definition)
    if re.fullmatch(r'W(?:8|16|32|64)\.t',t):return 0
    policy.require(re.fullmatch(r'W(?:8|16|32|64)\.t\s+Array(?:32|96|128|129|192|224|768|1152|1153)\.t',t),'unknown phase type: '+t)
    # Reuse the independently reviewed native array-cell rule.
    return kernel.type_cells(t)


def procedure(text,endpoint):
    module,name=endpoint.split('.')[-2:]
    found=[(head,body) for m,block in model_contract.syntax.modules(text) if m==module
           for p,head,body,_a,_b in model_contract.syntax.procedures(block) if p==name]
    policy.require(len(found)==1,'missing/ambiguous phase procedure: '+endpoint)
    return found[0]


def calls(body):
    result=[]
    for match in re.finditer(r'<@\s*([^;]+);',body):
        value=match.group(1).strip();policy.require(value.endswith(')'),'malformed phase call')
        depth=0;opening=None
        for i in range(len(value)-1,-1,-1):
            if value[i]==')':depth+=1
            elif value[i]=='(':
                depth-=1
                if depth==0:opening=i;break
        policy.require(opening is not None,'unbalanced phase call')
        result.append((match.start(),policy.compact(value[:opening])))
    for match in re.finditer(r'(?:^|(?<=[;{}]))\s*([A-Za-z_]\w*(?:\.\w+)+)\s*\([^;{}]*\)\s*;',body):
        result.append((match.start(),match.group(1)))
    return [target for _pos,target in sorted(result)]


def typed_environment(text,endpoint):
    header,raw=procedure(text,endpoint);opening=header.index('(');end=closing(header,opening)
    params={}
    for group in split_top(header[opening+1:end],','):
        if not group.strip():continue
        names,ty=group.split(':',1)
        for name in names.split():params[name]=ty.strip()
    ret=header[end+1:].strip().removeprefix(':').strip()
    policy.require(ret.endswith('='),'invalid phase result type');ret=ret[:-1].strip()
    env=dict(params);untyped=[]
    for match in re.finditer(r'\bvar\s+([^;]+);',raw):
        value=match.group(1)
        if ':' in value:
            names,ty=value.split(':',1)
            for name in re.findall(r'\w+',names):env[name]=ty.strip()
        else:untyped.extend(re.findall(r'\w+',value))
    if endpoint.startswith(('AHPrivateStore.','RTPrivateStore.')):env.update(st='ah_state',ledger='rt_profile')
    code=policy.without_comments(raw)
    for match in re.finditer(r'\breturn\s+(\w+)\s*;',code):
        if match.group(1) in untyped:env[match.group(1)]=ret
    return_types={'ROE.get':'W8.t Array192.t','ROF.get':'W8.t Array32.t','G.get':'W8.t Array192.t',
                  'O.h':'W8.t Array224.t','O.g':'W8.t Array192.t','ROH.get':'W8.t Array224.t',
                  'full':'W8.t Array224.t'}
    for match in re.finditer(r'\b(\w+)\s*<@\s*([\w.]+)\s*\(',code):
        name,target=match.groups()
        if name in untyped and target in return_types:env[name]=return_types[target]
    for match in re.finditer(r'\b(\w+)\s*<\$\s*uniform(32|192|224)\b',code):
        if match.group(1) in untyped:env[match.group(1)]='W8.t Array'+match.group(2)+'.t'
    if 'decode_typed' in code:
        for m in re.finditer(r'\|\s*Some\s+(\w+)\s*=>',code):env[m.group(1)]='typed_query'
        for constructor,ty in [('E','W8.t Array32.t'),('F','W8.t Array1152.t'),('G','W8.t Array1152.t'),('H','fo_h_input')]:
            for m in re.finditer(r'\|\s*'+constructor+r'\s+(\w+)\s*=>',code):env[m.group(1)]=ty
    if endpoint=='HistCipherOption.equal':
        for m in re.finditer(r'\|\s*Some\s+(\w+)\s*=>',code):env[m.group(1)]='W8.t Array1152.t'
    policy.require(all(name in env for name in untyped),'uninferred phase local type: '+endpoint)
    for ty in [*env.values(),ret]:type_cells(ty)
    return params,env,ret,raw


_PURE={'hist_zero_value','hist_lookup_default','sec_zero','payload_shared_key',
       'decode_typed','raw_xof_output','raw_join192','hash_join','raw_xof_max_output',
       'pke_ciphertext','pke_psi1','uniform32','uniform192','uniform224','rt_record'}
_LANGUAGE={'if','then','else','while','match','with','end','None','Some','oget','head','behead','return','true','false','E','F','G','H','witness'}
_FIELDS={'ah_rows','ah_pk','ah_suffix','ah_cstar'}
_ID=re.compile(r'[A-Za-z_]\w*(?:\.\w+)*')
_TOKEN=re.compile(r'[A-Za-z_]\w*|\d+|<@|<-|::|<>|/\\|\\/|[^\s]')


_PURE_COUNTS={
 'hist_zero_value':{'HistKeep.run':1},'hist_lookup_default':{'HistLookup.run':1},
 'sec_zero':{'AHActualOWReducer.run':1},'payload_shared_key':{'HistLookup.check':1},
 'decode_typed':{'AHOracles.raw':1,'FOGRaw.full':1},
 'raw_xof_output':{'AHOracles.raw':1,'FOGRaw.get':1},
 'raw_join192':{'FOGRawStreams.e':1,'FOGRawStreams.g':1},'hash_join':{'FOGRawStreams.f':1},
 'raw_xof_max_output':{'AHOracles.raw':1,'FOGRaw.get':1},
 'pke_ciphertext':{'AHActualINJReducer.run':1},'pke_psi1':{'AHActualINJReducer.run':2},
 'uniform32':{'FOGRawStreams.e':1,'FOGRawStreams.g':1,'AHActualTranscript.run':1},
 'uniform192':{'FOGRawStreams.f':1},'uniform224':{'FOGRawStreams.untyped':1},
 'rt_record':{'RTStoreOps.record':1},
}

def validate_fragment(body,env,endpoint):
    code=re.sub(r'\bvar\s+[^;]+;','',policy.without_comments(body))
    policy.require('++' not in code,'unpriced linear list append (++) in phase fragment')
    actual=calls(code)
    policy.require(actual==list(CALLS[endpoint]),'phase executable call-path drift: '+endpoint+' '+repr(actual))
    masked=code
    for target in sorted(set(actual),key=len,reverse=True):masked=masked.replace(target,' CALL ')
    allowed=set(env)|_PURE|_LANGUAGE|_FIELDS|{'CALL','RawXOFStreams.es','RawXOFStreams.fs','RawXOFStreams.gs','RawXOFStreams.other','SecGHistory.queries','notin'}
    unknown=set(_ID.findall(masked))-allowed
    policy.require(not unknown,'unknown/unpriced phase expression: '+endpoint+' '+repr(sorted(unknown)))
    policy.require(not re.search(r'\b(?:forall|exists|choice|choiceb|map|foldl|foldr|ofassoc|elems|fdom)\b',masked),'nonprimitive phase expression')
    for name in env:
        policy.require(not re.search(r'\b'+re.escape(name)+r'\s*\(',masked),'functional use of phase local: '+name)
    residue=_ID.sub('',masked)
    policy.require(not re.search(r'[^\s\d;(){}\[\],.\x60|<>=$@+*:/\\!\-]',residue),'unsupported phase source token')
    for op,uses in _PURE_COUNTS.items():
        policy.require(len(re.findall(r'\b'+op+r'\b',code))==uses.get(endpoint,0),'unexpanded/repeated phase operation: '+endpoint+' '+op)
    comparison=re.sub(r'\{\|.*?\|\}',' RECORD ',code,flags=re.S)
    if endpoint in ('SecExtract.run','CostExtract.run'):
        pattern=r'\(\s*oget\s+candidate\s*\)\s*\.\`2\s*<>\s*oget\s+excluded'
        policy.require(len(re.findall(pattern,comparison))==1,'fixed 768-word exclusion comparison drift')
        comparison=re.sub(pattern,' WORD_COMPARE ',comparison)
    comparison=re.sub(r'\b\w+\s*(?:<>|=)\s*(?:None\b|\[\])',' TAG_COMPARE ',comparison)
    policy.require(not re.search(r'<>|(?<![<>=])=(?![=>])',comparison),'unpriced scalar/compound value equality in phase fragment')
    if 'pke_ciphertext' in code or 'pke_psi1' in code:
        policy.require(endpoint=='AHActualINJReducer.run','mathematical crypto op outside reviewed ghost projection')
    if 'rt_record' in code:
        policy.require(endpoint=='RTStoreOps.record' and re.search(r'p\s*<-\s*rt_record\s+p\b',code),'non-ghost use of ledger helper')
    policy.require(not re.search(r'\bsize\b',code),'unexpanded linear list-size computation')
    if 'witness' in code:policy.require(code.count('witness')==len(re.findall(r'\bhead\s+witness\b',code)),'unpriced witness allocation')
    return code


def separate_loop(code,endpoint):
    found=list(re.finditer(r'\bwhile\s*\(',code))
    policy.require(len(found)==(1 if endpoint in LOOPS else 0),'phase loop inventory drift: '+endpoint)
    if not found:return code,'',0
    m=found[0];op=code.index('(',m.start());end=closing(code,op)
    cond=code[op+1:end];start=code.find('{',end)
    policy.require(start>=0 and not code[end+1:start].strip(),'phase loop header drift')
    finish=closing(code,start,'{','}')
    policy.require(policy.compact(cond)==LOOPS[endpoint],'phase loop/control attribution drift: '+endpoint)
    return code[:m.start()]+' '+cond+' '+code[finish+1:],cond+' '+code[start+1:finish],1


def block_fee(code,env):
    counts=Counter(re.findall(r'[A-Za-z_]\w*',code));cells={name:type_cells(ty) for name,ty in env.items() if type_cells(ty)}
    refs={name:counts[name] for name in cells if counts[name]}
    initializers={'hist_zero_value':224,'hist_lookup_default':352,'sec_zero':768}
    init_calls=sum(counts[x] for x in initializers);init_cells=sum(counts[x]*n for x,n in initializers.items())
    for match in re.finditer(r'\bhead\s+witness\s+(\w+)',code):
        ty=env.get(match.group(1),'');policy.require(ty.endswith(' list'),'head witness has unknown element type')
        n=type_cells(ty[:-5]);policy.require(n==1152,'unreviewed head witness payload')
        init_calls+=1;init_cells+=n
    guards=sum(counts[x] for x in ('if','match'))
    list_ops={'head':counts['head'],'behead':counts['behead'],'cons':code.count('::')}
    copied=sum(cells[name]*n for name,n in refs.items())
    tokens=len(_TOKEN.findall(code))
    total=tokens+guards+list_ops['head']+list_ops['behead']+3*copied+5*init_cells+8*init_calls
    return {'local_scalar_ops':tokens,'guards':guards,'list_ops':list_ops,'array_reference_occurrences':refs,
            'array_copy_cells':copied,'initializer_cells':init_cells,'initializer_calls':init_calls,'numeric_local_upper':total}


def numeric_entry(text,endpoint,record):
    params,env,ret,raw=typed_environment(text,endpoint)
    code=validate_fragment(raw,env,endpoint);fixed,visit,loops=separate_loop(code,endpoint)
    fixed_fee=block_fee(fixed,env);visit_fee=block_fee(visit,env)
    for fee in (fixed_fee,visit_fee):fee['guards']+=loops;fee['numeric_local_upper']+=loops
    incoming=sum(type_cells(ty) for ty in params.values());outgoing=type_cells(ret)
    fixed_fee['array_copy_cells']+=incoming+outgoing
    fixed_fee['array_boundary_cells']={'entry':incoming,'return':outgoing}
    fixed_fee['numeric_local_upper']+=3*(incoming+outgoing)
    expected_types={name:type_cells(ty) for name,ty in env.items() if type_cells(ty)}
    for name,value in [('array_value_cells',expected_types),('fixed_breakdown',fixed_fee),('per_visit_breakdown',visit_fee),
                       ('fixed_local_upper',fixed_fee['numeric_local_upper']),('per_visit_local_upper',visit_fee['numeric_local_upper']),('loop_count',loops)]:
        policy.require(record.get(name)==value,'independent phase '+name+' mismatch: '+endpoint+' '+repr(value))
    return {'fixed':fixed_fee['numeric_local_upper'],'visit':visit_fee['numeric_local_upper'],'entry_cells':incoming,'return_cells':outgoing}



CRITICAL_BODIES = {
 'AHOracles.raw': 'if(0<=outlen<=raw_xof_max_output){\n match decode_typed input with\n | None => {result<@O.raw(input,outlen);}\n | Some query => {match query with\n | E seed => {result<@O.raw(input,outlen);}\n | F pk => {result<@O.raw(input,outlen);}\n | G serialized => {result<@O.raw(input,outlen);}\n | H payload => {hout<@AHRecordH(S,O).get(payload);result<-Some(raw_xof_output outlen hout);}\n end;}end;\n }else{result<@O.raw(input,outlen);}return result;',
 'FOGRaw.get':'result<-None;if(0<=outlen<=raw_xof_max_output){stream<@full(input);result<-Some(raw_xof_output outlen stream);}return result;',
 'SecGLogged.get':'SecGHistory.queries<-input::SecGHistory.queries;y<@G.get(input);return y;',
 'AHRecordH.get':'hout<@O.h(input);S.record(input,hout);return hout;',
 'AHActualTranscript.run':'SecGHistory.init();key<$uniform32;ignored<@AHActualPhase(S,A,SecGLogged(FOGActual)).run(pk,ct,key);return SecGHistory.queries;',
 'SecAuxSetup.run':'ROMInit.init();RawXOFStreams.init();ignored<@ROF.get(pk);',
 'FOHashG.run':'(serialized,input)<@ACWC2GPrepare.run(r);pad<@G.shake(input);return pad;',
 'ACWC2GPrepare.run':'rhat<@NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);(serialized,input)<@NTRUPlus768DecapMessagePrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(witness,witness,rhat);return(serialized,input);',
 'FOGHash.shake':'y<@G.get(peel1153 input);return y;',
 'SOTPEncode.run':'code<@NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(witness,msg,pad);return code;',
 'SimEncrypt.run':'r<@NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail hout);pad<@FOHashG(FOGHash(G)).run(r);code<@SOTPEncode.run(msg,pad);ct<@PKEEnc.run(pk,code,r);return ct;',
}
CALLBACK = ('HistKeep.run','HistReverse.run','HistTable.put','HistCipherOption.equal','HistLookup.run',
 'AHPublicG.get','AHRecordH.get','AHOracles.raw','AHDecap.decap','AHPrivateStore.snapshot','AHPrivateStore.record',
 'FOGRawStreams.e','FOGRawStreams.f','FOGRawStreams.g','FOGRawStreams.h','FOGRawStreams.untyped','FOGRaw.full','FOGRaw.get',
 'SecGLogged.get','SimOracles.g','SharedCCAOracles.e','SharedCCAOracles.f','RTStoreOps.record','RTPrivateStore.snapshot','RTPrivateStore.record')
SETUP = ('AHWrapper.guess','AHActualPhase.run','AHActualTranscript.run','SecAuxSetup.run','AHActualINJReducer.run',
 'AHActualOWReducer.run','SecINJAuxAdapter.run','SecOWAuxAdapter.run','AHPrivateStore.init','RTStoreOps.init','RTPrivateStore.init')
LOGGED = ('AHPublicG.get','SimOracles.g','SecGLogged.get')


def wrapper_entries(sources,entries):
    result={}
    for endpoint,op in WRAPPERS.items():
        text=sources[endpoint];r=entries[endpoint]
        params,_env,ret=kernel.signature(text,endpoint)
        incoming=sum(type_cells(ty) for ty in params.values());outgoing=type_cells(ret)
        fields=len(split_top(ret.strip().strip('()'),'*'))
        pieces={'entry_array_cells':incoming,'return_array_cells':outgoing,'arity':len(params),'return_fields':fields,
          'entry_cost':3*incoming,'return_cost':fields+3*outgoing,'caller_frame_and_binding':2+len(params)+3*outgoing}
        total=pieces['entry_cost']+pieces['return_cost']+pieces['caller_frame_and_binding']
        pieces.update(fixed_local_upper=total,per_visit_local_upper=0,executions_per_encryption=1,price_op=op)
        policy.require(all(r.get(k)==v for k,v in pieces.items()),'wrapper boundary/signature charge drift: '+endpoint)
        policy.require(calls(cal.raw_body(text,endpoint))==list(CALLS[endpoint]),'inlined wrapper call mapping drift')
        result[endpoint]={**pieces,'fixed':total,'visit':0}
    sim=entries['SimEncrypt.run'];direct=[(v['callee'],v['count']) for v in sim['expected_direct_calls']]
    policy.require(direct==[(x,1) for x in CALLS['SimEncrypt.run']],'SimEncrypt direct call coverage drift')
    nested=[(v['parent'],v['callee'],v['count']) for v in sim['expected_nested_calls']]
    policy.require(nested==[('FOHashG.run','ACWC2GPrepare.run',1),('FOHashG(FOGHash(G)).run','FOGHash(G).shake',1)],'SimEncrypt nested wrapper coverage drift')
    policy.require(sim.get('wrapper_total')==sum(v['fixed'] for v in result.values()),'SimEncrypt wrapper aggregate drift')
    return result


def rhs(text,name):
    decl=declaration(text,'op',name)
    match=re.search(r'(?<![<>=])=(?![=>])',decl)
    policy.require(match,'phase operation lacks definition: '+name)
    return policy.compact(decl[match.end():-1])


def semantic_support(data):
    templates={
      'List.ec':{'size':"op size(xs:'a list)=with xs=[]=>0 with xs=y::ys=>1+(size ys).",
                 'nth':"op nth x(xs:'a list)n:'a=with xs=[]=>x with xs=y::ys=>if n=0 then y else(nth x ys(n-1)).",
                 'take':"op take n(xs:'a list)=with xs=[]=>[] with xs=y::ys=>if n<=0 then[] else y::take(n-1)ys."},
      'JArray.ec':{'of_list':"op of_list(dfl:'a)(l:'a list)=init(fun i=>nth dfl l i).",
                   'to_list':"op to_list(t:'a t)=mkseq(fun i=>t.[i])size."}}
    found={};external=[]
    for record in data.get('semantic_support',[]):
        p=Path(record['source']);policy.require(p.is_absolute() and p.is_file() and not p.is_symlink(),'invalid phase semantic support')
        policy.require(p.name in templates and p.name not in found,'unreviewed/duplicate phase semantic support')
        policy.require(policy.sha(p.read_bytes())==record['sha256'],'phase semantic support source drift')
        text=p.read_text()
        for name,expected in templates[p.name].items():
            if p.name=='JArray.ec':
                declarations=re.findall(r'(?ms)^\s*op\s+'+name+r'\b.*?(?<!\.)\.\s*(?=\n|$)',policy.without_comments(text))
                selected=[d for d in declarations if "'a" in d]
                policy.require(len(selected)==1,'missing/ambiguous polymorphic array semantics: '+name)
                actual=selected[0]
            else:actual=declaration(text,'op',name)
            policy.require(policy.compact(actual)==policy.compact(expected),'recursive list/array cost semantics changed: '+name)
        found[p.name]=p;external.append({'path':str(p),'sha256':policy.sha(p.read_bytes())})
    policy.require(set(found)==set(templates),'recursive list/array source support incomplete')
    return external


def protocol_bridges(sources,source_blocks):
    """The cost ledger may be erased; protocol state and G history may not."""
    checks={
      'RTOracles':{
        'RTOracles.e':'S.charge_call(false,0);out<@O.e(input);return out;',
        'RTOracles.f':'S.charge_call(false,0);out<@O.f(input);return out;',
        'RTOracles.g':'S.charge_call(true,0);out<@O.g(input);return out;',
        'RTOracles.h':'S.charge_call(false,0);out<@AHRecordH(S,O).get(input);return out;',
        'RTOracles.raw':'S.charge_call(rt_raw_g_exec input outlen,size input);out<@AHOracles(S,O).raw(input,outlen);return out;',
        'RTDecap.decap':'S.charge_call(false,0);st<@S.snapshot();out<@HistLookup(AHPublicG(O)).run(st.`ah_rows,st.`ah_pk,st.`ah_suffix,st.`ah_cstar,ct);S.charge_decap(out.`2,out.`3,out.`4);return out.`1;'},
      'RTAdaptive':{
        'RTWrapper.guess':'suffix<@O.f(pk);S.init(pk,suffix,Some ct);answer<@A(RTOracles(S,O),RTDecap(S,O)).guess(pk,ct,key);return answer;',
        'RTActualPhase.run':'suffix<@ROF.get(pk);answer<@RTWrapper(S,A,AHActualOracles(G),AHRejectD).guess(pk,ct,key);return answer;',
        'RTTranscript.run':'SecGHistory.init();key<$uniform32;ignored<@RTActualPhase(S,A,SecGLogged(FOGActual)).run(pk,ct,key);profile<@S.metrics();return(SecGHistory.queries,profile);'},
      'RTFinal':{
        'RTPrivateStore.reset_cost':'ledger<@RTStoreOps.reset_cost();',
        'RTPrivateStore.metrics':'return ledger;',
        'RTPrivateStore.charge_call':'ledger<@RTStoreOps.charge_call(ledger,is_g,bytes);',
        'RTPrivateStore.charge_decap':'ledger<@RTStoreOps.charge_decap(ledger,visits,encryptions,comparisons);',
        'RTPrivateStore.charge_extract':'ledger<@RTStoreOps.charge_extract(ledger,visits);'},
    }
    endpoints=[];forwarding=[]
    for file,procs in checks.items():
        p=policy.PROOF/('NTRUPlus768'+file+'.ec');text=p.read_text()
        for endpoint,expected in procs.items():
            policy.require(manual.normalize(cal.raw_body(text,endpoint))==policy.compact(expected),'actual phase/ghost erasure boundary drift: '+endpoint)
            endpoints.append(str(p.relative_to(policy.ROOT))+':'+endpoint)
            if endpoint.startswith('RTOracles.') or endpoint=='RTDecap.decap':
                params,env,ret,body=typed_environment(text,endpoint)
                erased=re.sub(r'S\s*\.\s*charge_(?:call|decap)\s*\([^;]*\)\s*;','',re.sub(r'\bvar\s+[^;]+;','',policy.without_comments(body)))
                fee=block_fee(erased,env)['numeric_local_upper']+3*(sum(type_cells(t) for t in params.values())+type_cells(ret))
                # AHPublicG's conservative fixed allowance is in the union
                # callback price, while internal G forwarding is paid again
                # by the distinct per-encryption logged-G bucket.
                proxy='AHDecap.decap' if endpoint=='RTDecap.decap' else 'AHPublicG.get'
                ceiling=source_blocks[proxy]['fixed']
                policy.require(fee<=ceiling,'actual forwarding wrapper exceeds calibrated callback union: '+endpoint)
                forwarding.append({'endpoint':endpoint,'erased_local_cost':fee,'callback_union_proxy':proxy,'ceiling':ceiling})
    keyfile=policy.BASE/'kem_history_refinement/NTRUPlus768HistKey.ec'
    keytext=keyfile.read_text()
    for endpoint,template in [('HistKey.equal','key'),('HistKey.suffix','suffix'),('HistKey.cipher','cipher')]:
        expected=re.sub(r'work\s*<-\s*[^;]+;','',manual.expected_primitive(template))
        expected=expected.replace('return(same,work);','return(same,comparisons);')
        policy.require(manual.normalize(cal.raw_body(keytext,endpoint))==policy.compact(expected),'actual comparator differs from calibrated finite scan: '+endpoint)
        endpoints.append(str(keyfile.relative_to(policy.ROOT))+':'+endpoint)
    original=(policy.BASE/'kem_adaptive_history/NTRUPlus768AHActualReduction.ec').read_text()
    module=[b for n,b in model_contract.syntax.modules(original) if n=='AHActualOracles']
    policy.require(len(module)==1 and policy.compact(module[0])==policy.compact('proc e=SharedCCAOracles.e proc f=SharedCCAOracles.f proc g=SimOracles(G,SimHActual).g proc h=ROH.get proc raw=FOGRaw(G).get'),'actual oracle alias path drift')
    eager=policy.compact((policy.BASE/'kem_modified_fo/NTRUPlus768FOEagerG.ec').read_text())
    policy.require('moduleFOGActual:FOGPort={procget=ROG.get}.' in eager,'G path is not the reviewed ideal ROG endpoint')
    extras={
      'kem_rom_oracle/NTRUPlus768ROMOracles.ec':{'ROMInit.init':'ROE.init();ROF.init();ROG.init();ROH.init();'},
      'kem_indcca_game/NTRUPlus768RawXOFStreams.ec':{'RawXOFStreams.init':'es<-empty;fs<-empty;gs<-empty;other<-empty;'},
      'kem_acwc2_security/NTRUPlus768SecGOracles.ec':{'SecGHistory.init':'queries<-[];'}}
    for file,procs in extras.items():
        text=(policy.BASE/file).read_text()
        for endpoint,expected in procs.items():
            policy.require(manual.normalize(cal.raw_body(text,endpoint))==policy.compact(expected),'ideal setup/list initialization drift: '+endpoint)
            endpoints.append(PREFIX+file+':'+endpoint)
    sampling=(policy.BASE/'kem_indcca_game/NTRUPlus768RawXOFSampling.ec').read_text()
    policy.require(rhs(sampling,'raw_xof_max_output')=='224','raw maximum output changed')
    tail=(policy.BASE/'decap_complete/NTRUPlus768DecapCompleteSpec.ec').read_text()
    expected='op complete_hash_tail(h:W8.t Array224.t):W8.t Array192.t=Array192.init(fun i=>h.[32+i]).'
    policy.require(policy.compact(declaration(tail,'op','complete_hash_tail'))==policy.compact(expected),'Sim fixed tail copy semantics drift')
    bounds=(policy.PROOF/'NTRUPlus768RTBounds.ec').read_text()
    charge='c.`pc_call*p.`rp_q+c.`pc_input*p.`rp_b+c.`pc_visit*rt_visits p+c.`pc_compare*rt_comparisons p+c.`pc_cons*(p.`rp_alloc+rt_g_length p)+c.`pc_encrypt*p.`rp_enc+c.`pc_candidate*p.`rp_xvisits+c.`pc_extract_init*p.`rp_xcalls'
    envelope='c.`pc_call*q+c.`pc_input*b+c.`pc_visit*(3*q*q+q)+c.`pc_compare*(1248*q*q+1152*q)+c.`pc_cons*(2*q*q+q)+c.`pc_encrypt*(q*q)+c.`pc_candidate*(q*q+q)+c.`pc_extract_init'
    for name,value in [('rt_phase_charge',charge),('rt_q_envelope',envelope)]:
        policy.require(rhs(bounds,name)==policy.compact(value),'phase charge/envelope no longer accounts for the actual ledger: '+name)
        endpoints.append(PREFIX+'kem_runtime_bound/NTRUPlus768RTBounds.ec:op.'+name)
    return endpoints,forwarding


def aggregate(data,source_blocks,wrappers):
    f=lambda e:source_blocks[e]['fixed'];v=lambda e:source_blocks[e]['visit']
    callback=sum(f(e) for e in CALLBACK);setup=sum(f(e) for e in SETUP)
    logged=sum(f(e) for e in LOGGED)+1
    history_cons=3*(type_cells('hist_entry')+2)+8;g_cons=3*(1152+2)+8
    visits={'keep':v('HistKeep.run'),'reverse':v('HistReverse.run'),
       'lookup':v('HistLookup.run')+f('HistLookup.check')+f('HistCipherOption.equal')+(5*32+8),
       'extract':v('CostExtract.run')}
    visit=1<<(max(visits.values())-1).bit_length();logged_cap=1<<(logged-1).bit_length()
    expected_aggregate={
      'callback_fixed':{'entries':list(CALLBACK),'sum_local_upper':callback,'plus_stream_rule':'rt_phase_stream_fixed','decoder_calls':2,'prefix_calls':1},
      'setup_fixed':{'entries':list(SETUP),'sum_local_upper':setup,'extra_typed_F':3,'extra_uniform32_units':6*32+2,'extra_ideal_initialization_units':8*4},
      'visit':{'choices':visits,'rounded_upper':visit},
      'put_fixed':{'entries':['HistTable.put','HistKeep.run','HistReverse.run'],'total':sum(f(e) for e in ('HistTable.put','HistKeep.run','HistReverse.run'))},
      'lookup_fixed':{'entries':['HistLookup.run','HistCipherOption.equal'],'total':f('HistLookup.run')+f('HistCipherOption.equal')},
      'extract_fixed':{'entries':['CostExtract.run'],'total':f('CostExtract.run')},
      'logged_G_fixed':{'entries':list(LOGGED),'extra_ideal_endpoint':1,'total':logged,'rounded_upper':logged_cap},
      'encrypt_wrappers':{'entries':list(WRAPPERS),'total':sum(r['fixed'] for r in wrappers.values()),'separate_from_logged_G':True,'common_native_calls_not_repriced':True}}
    policy.require(data.get('bucket_aggregation')==expected_aggregate,'independent phase bucket composition drift')
    raw_rules={'decoder_calls_max':2,'size_calls_per_decoder_max':4,'size_per_cell':8,'size_fixed':5,
      'typed_array_sizes':[32,129,1153],'max_initializer_cells':1153,'nth_per_index':10,'nth_fixed':8,
      'of_list_fixed':5,'of_list_linear':10,'of_list_nth_calls':'N','of_list_nth_max_index':'N',
      'decode_fixed_overhead':64,'peel_copy_per_max_cell':24,'prefix_cells':224,'prefix_per_cell':24,
      'prefix_fixed':32,'raw_input_coefficient':64,'zero_output_still_full_backend':True}
    policy.require(data.get('raw_numeric_rules')==raw_rules,'raw list/array expansion rule drift')
    outputs=data.get('outputs',[])
    policy.require(len(outputs)==2 and outputs[0].get('required_final_substitutions')==
      {'C_encrypt':'rt_kernel_sim_encrypt_bound','C_candidate':'rt_kernel_candidate_bound'} and
      outputs[1].get('price_op')=='rt_concrete_phase_prices' and outputs[1].get('free_kernel_parameters')==[],
      'phase final price has an unclosed kernel parameter')
    phase=(policy.PROOF/'NTRUPlus768RTPhaseCost.ec').read_text()
    manual.check(require_complete=True)
    primitive=(policy.PROOF/'NTRUPlus768RTPrimitiveCost.ec').read_text()
    for name,value in [('rt_byte_compare_steps','18*n+5'),('rt_word_compare_steps','16*n+5'),('rt_key_compare_steps','2629')]:
        policy.require(rhs(primitive,name)==value,'primitive comparison cost formula drift')
    compare=max((2629+127)//128,(18*32+5+31)//32,(18*1152+5+1151)//1152)
    ops={
      'rt_phase_copy':'3*n','rt_phase_size':'8*n+5','rt_phase_nth':'10*n+8',
      'rt_phase_of_list':'5+10*n+n*rt_phase_nth n','rt_phase_decode_fixed':'64+rt_phase_of_list 1153+24*1153',
      'rt_phase_decode':'4*rt_phase_size n+rt_phase_decode_fixed','rt_phase_prefix_fixed':'32+24*224',
      'rt_phase_stream_fixed':'64+4*(rt_phase_copy(1152+224)+8)+32*224',
      'rt_phase_store_fixed':'+'.join(str(f(e)) for e in ('AHPrivateStore.record','RTStoreOps.record','RTPrivateStore.record','AHPrivateStore.snapshot','RTPrivateStore.snapshot')),
      'rt_phase_put_fixed':'+'.join(str(f(e)) for e in ('HistTable.put','HistKeep.run','HistReverse.run')),
      'rt_phase_lookup_fixed':'+'.join(str(f(e)) for e in ('HistLookup.run','HistCipherOption.equal')),
      'rt_phase_extract_fixed':str(f('CostExtract.run')),
      'rt_phase_history_cons':'3*(352+2)+8','rt_phase_g_cons':'3*(1152+2)+8',
      'rt_phase_keep_visit':str(visits['keep']),'rt_phase_reverse_visit':str(visits['reverse']),
      'rt_phase_lookup_visit':'+'.join(map(str,(v('HistLookup.run'),f('HistLookup.check'),f('HistCipherOption.equal'),5*32+8))),
      'rt_phase_extract_visit':str(visits['extract']),'rt_phase_visit':str(visit),
      'rt_phase_compare':str(compare),'rt_phase_cons':'rt_phase_g_cons','rt_phase_input':'64',
      'rt_phase_callback_fixed':str(callback),
      'rt_phase_call':'2*rt_phase_decode_fixed+40+rt_phase_prefix_fixed+rt_phase_stream_fixed+rt_phase_callback_fixed',
      'rt_phase_logged_g_fixed':str(logged_cap),
      'rt_phase_setup_fixed':str(setup)+'+3*'+str(f('SharedCCAOracles.f'))+'+194+32',
      'rt_phase_wrapper_boundary':'3*inputs+(return_fields+3*outputs)+(2+arity+3*outputs)',
      'rt_phase_encrypt_wrapper_fixed':'rt_phase_fohash_boundary+rt_phase_gprepare_boundary+rt_phase_foghash_boundary+rt_phase_sotp_boundary',
      'rt_calibrated_phase_prices':'{|pc_call=rt_phase_call;pc_input=rt_phase_input;pc_visit=rt_phase_visit;pc_compare=rt_phase_compare;pc_cons=rt_phase_cons;pc_encrypt=c_encrypt+rt_phase_logged_g_fixed+rt_phase_encrypt_wrapper_fixed;pc_candidate=c_candidate+rt_word_compare_steps 768;pc_extract_init=rt_phase_setup_fixed+rt_phase_extract_fixed|}',
      'rt_phase_put_body':'rt_phase_put_fixed+rt_phase_visit*(n+k)+rt_key_compare_steps*n+rt_phase_history_cons*(2*k+1)',
      'rt_phase_lookup_body':'rt_phase_lookup_fixed+rt_phase_visit*v+rt_phase_compare*comparisons+(c_encrypt+rt_phase_logged_g_fixed+rt_phase_encrypt_wrapper_fixed)*k+rt_phase_g_cons*k',
      'rt_phase_extract_body':'rt_phase_extract_fixed+(rt_phase_visit+c_candidate+rt_word_compare_steps 768)*visits',
      'rt_phase_callback_body':'2*rt_phase_decode n+rt_phase_prefix_fixed+rt_phase_stream_fixed+rt_phase_callback_fixed',
      'rt_concrete_phase_prices':'rt_calibrated_phase_prices rt_kernel_sim_encrypt_bound rt_kernel_candidate_bound'}
    for endpoint,op in WRAPPERS.items():
        w=wrappers[endpoint];ops[op]='rt_phase_wrapper_boundary '+' '.join(str(w[k]) for k in ('entry_array_cells','return_array_cells','arity','return_fields'))
    for name,expected in ops.items():
        policy.require(rhs(phase,name)==policy.compact(expected),'phase source-derived price/formula drift: '+name)
    import sim_calibration
    sim=sim_calibration.check(require_complete=False);closed=sim['closed_bounds']
    of_list=lambda n:5+10*n+n*(10*n+8)
    decode=64+of_list(1153)+24*1153
    prices={'pc_call':2*decode+40+32+24*224+64+4*(3*(1152+224)+8)+32*224+callback,
      'pc_input':64,'pc_visit':visit,'pc_compare':compare,'pc_cons':max(history_cons,g_cons),
      'pc_encrypt':closed['rt_kernel_sim_encrypt_bound']+logged_cap+sum(w['fixed'] for w in wrappers.values()),
      'pc_candidate':closed['rt_kernel_candidate_bound']+16*768+5,
      'pc_extract_init':setup+3*f('SharedCCAOracles.f')+(6*32+2)+(8*4)+f('CostExtract.run')}
    expected='lemma rt_concrete_phase_price_values:'+ '/\\'.join('rt_concrete_phase_prices.`'+k+'='+str(v) for k,v in prices.items())+'.'
    policy.require(cal.lemma_declaration(phase,'rt_concrete_phase_price_values')==policy.compact(expected),'closed price theorem changed')
    for name,decl in CERTIFICATES.items():
        policy.require(cal.lemma_declaration(phase,name)==decl,'phase semantic/count/cost theorem changed: '+name)
    return prices

CERTIFICATES = {'rt_phase_encrypt_wrapper_calibration': 'lemmart_phase_encrypt_wrapper_calibration:rt_phase_fohash_boundary=3460/\\rt_phase_gprepare_boundary=16139/\\rt_phase_foghash_boundary=4615/\\rt_phase_sotp_boundary=5477/\\rt_phase_encrypt_wrapper_fixed=29691.', 'rt_phase_compare_calibration': 'lemmart_phase_compare_calibration:rt_key_compare_steps<=rt_phase_compare*128/\\rt_byte_compare_steps32<=rt_phase_compare*32/\\rt_byte_compare_steps1152<=rt_phase_compare*1152.', 'rt_phase_node_calibration': 'lemmart_phase_node_calibration:0<=rt_phase_history_cons<=rt_phase_cons/\\0<=rt_phase_g_cons<=rt_phase_cons.', 'rt_phase_visit_calibration': 'lemmart_phase_visit_calibration:0<=rt_phase_keep_visit<=rt_phase_visit/\\0<=rt_phase_reverse_visit<=rt_phase_visit/\\0<=rt_phase_lookup_visit<=rt_phase_visit/\\0<=rt_phase_extract_visit<=rt_phase_visit.', 'rt_phase_raw_linear': 'lemmart_phase_raw_linearn:0<=n=>rt_phase_callback_bodyn=rt_phase_call+rt_phase_input*n.', 'rt_phase_of_list_bound': 'lemmart_phase_of_list_boundn:0<=n<=1153=>0<=rt_phase_of_listn<=rt_phase_of_list1153.', 'rt_phase_fixed_nonnegative': 'lemmart_phase_fixed_nonnegative:0<=rt_phase_call/\\0<=rt_phase_input/\\0<=rt_phase_visit/\\0<=rt_phase_compare/\\0<=rt_phase_cons/\\0<=rt_phase_setup_fixed/\\0<=rt_phase_extract_fixed/\\0<=rt_phase_logged_g_fixed/\\0<=rt_phase_encrypt_wrapper_fixed.', 'rt_calibrated_prices_ok': 'lemmart_calibrated_prices_okcecc:0<=ce=>0<=cc=>rt_prices_ok(rt_calibrated_phase_pricescecc).', 'rt_phase_put_bound': 'lemmart_phase_put_boundceccnk:0<=n=>0<=k=>rt_phase_put_bodynk<=(rt_calibrated_phase_pricescecc).`pc_call+(rt_calibrated_phase_pricescecc).`pc_visit*(n+k)+(rt_calibrated_phase_pricescecc).`pc_compare*(128*n)+(rt_calibrated_phase_pricescecc).`pc_cons*(2*k+1).', 'rt_phase_lookup_bound': 'lemmart_phase_lookup_boundceccvkcomparisons:rt_phase_lookup_bodycevkcomparisons<=(rt_calibrated_phase_pricescecc).`pc_call+(rt_calibrated_phase_pricescecc).`pc_visit*v+(rt_calibrated_phase_pricescecc).`pc_compare*comparisons+(rt_calibrated_phase_pricescecc).`pc_encrypt*k+(rt_calibrated_phase_pricescecc).`pc_cons*k.', 'rt_phase_extract_bound': 'lemmart_phase_extract_boundceccv:rt_phase_setup_fixed+rt_phase_extract_bodyccv<=(rt_calibrated_phase_pricescecc).`pc_extract_init+(rt_calibrated_phase_pricescecc).`pc_visit*v+(rt_calibrated_phase_pricescecc).`pc_candidate*v.', 'rt_hist_put_source_certificate': 'lemmart_hist_put_source_certificatececcx0y0xs0:hoare[HistTable.put:x=x0/\\y=y0/\\xs=xs0==>rt_phase_put_body(sizexs0)(sizeres.`1-1)<=(rt_calibrated_phase_pricescecc).`pc_call+(rt_calibrated_phase_pricescecc).`pc_visit*res.`2+(rt_calibrated_phase_pricescecc).`pc_compare*res.`3+(rt_calibrated_phase_pricescecc).`pc_cons*(2*(sizeres.`1-1)+1)].', 'rt_hist_lookup_source_certificate': 'lemmart_hist_lookup_source_certificate(G<:FOGPort)cecc:hoare[HistLookup(G).run:true==>rt_phase_lookup_bodyceres.`2res.`3res.`4<=(rt_calibrated_phase_pricescecc).`pc_call+(rt_calibrated_phase_pricescecc).`pc_visit*res.`2+(rt_calibrated_phase_pricescecc).`pc_compare*res.`4+(rt_calibrated_phase_pricescecc).`pc_encrypt*res.`3+(rt_calibrated_phase_pricescecc).`pc_cons*res.`3].', 'rt_extract_source_certificate': 'lemmart_extract_source_certificatececcpk0ct0excluded0queries0:hoare[CostExtract.run:pk=pk0/\\ct=ct0/\\excluded=excluded0/\\queries=queries0==>0<=res.`2/\\rt_phase_setup_fixed+rt_phase_extract_bodyccres.`2<=(rt_calibrated_phase_pricescecc).`pc_extract_init+(rt_calibrated_phase_pricescecc).`pc_visit*res.`2+(rt_calibrated_phase_pricescecc).`pc_candidate*res.`2].', 'rt_calibrated_phase_bound': 'lemmart_calibrated_phase_boundceccp:0<=ce=>0<=cc=>rt_cost_okp=>p.`rp_xcalls<=1=>rt_phase_charge(rt_calibrated_phase_pricescecc)p<=rt_phase_envelope(rt_calibrated_phase_pricescecc)p.`rp_hp.`rp_dp.`rp_gp.`rp_qp.`rp_b.', 'rt_calibrated_phase_q_bound': 'lemmart_calibrated_phase_q_boundceccp:0<=ce=>0<=cc=>rt_cost_okp=>p.`rp_xcalls<=1=>p.`rp_h+p.`rp_d+p.`rp_g<=p.`rp_q=>rt_phase_charge(rt_calibrated_phase_pricescecc)p<=rt_q_envelope(rt_calibrated_phase_pricescecc)p.`rp_qp.`rp_b.', 'rt_concrete_phase_prices_ok': 'lemmart_concrete_phase_prices_ok:rt_prices_okrt_concrete_phase_prices.', 'rt_concrete_phase_q_bound': 'lemmart_concrete_phase_q_boundp:rt_cost_okp=>p.`rp_xcalls<=1=>p.`rp_h+p.`rp_d+p.`rp_g<=p.`rp_q=>rt_phase_chargert_concrete_phase_pricesp<=rt_q_envelopert_concrete_phase_pricesp.`rp_qp.`rp_b.'}

def metadata_path(require_complete):
    portable=policy.TEST/'calibration/manual-phase.json'
    if portable.is_file():return portable
    policy.require(not require_complete,'phase calibration portable freeze missing')
    return None


def check(require_complete=True):
    metadata=metadata_path(require_complete)
    if metadata is None:return {'status':'PENDING','endpoints':[],'closed_prices':{},'external_inputs':[]}
    return _check_record(json.loads(metadata.read_text()),require_complete)


def _check_record(data,require_complete=False):
    policy.require(data.get('schema')==1 and data.get('kind')=='manual-phase','unknown phase metadata format')
    policy.require(data.get('model')=='unit-cost-integer-word-ideal-rom-v1','unknown phase model')
    if require_complete:policy.require(data.get('status')=='FROZEN','phase calibration is not frozen')
    indexed={}
    for entry in data.get('entries',[]):
        endpoint=('op.'+entry['op']) if 'op' in entry else entry.get('module','')+'.'+entry.get('procedure','')
        policy.require(endpoint not in indexed,'duplicate phase endpoint')
        policy.require(INVENTORY.get(endpoint)==entry.get('source'),'unreviewed phase endpoint/source: '+endpoint)
        indexed[endpoint]=entry
    policy.require(set(indexed)==set(INVENTORY),'whole adaptive phase coverage incomplete')
    sources={name:cal.path(path).read_text() for name,path in INVENTORY.items()}
    pure_owners={name:INVENTORY.get('op.'+name) for name in _PURE}
    pure_owners['raw_xof_max_output']=PREFIX+'kem_indcca_game/NTRUPlus768RawXOFSampling.ec'
    for name in ('oget','head','behead','size','nth','take'):pure_owners[name]=None
    module_owners={endpoint.split('.')[0]:path for endpoint,path in INVENTORY.items() if not endpoint.startswith('op.')}
    seen=set()
    for endpoint,text in sources.items():
        path=INVENTORY[endpoint]
        if path in seen:continue
        seen.add(path);code=policy.without_comments(text)
        policy.require(not re.search(r'\b(?:op|pred|abbrev)\s+(?:\[[^]]*\]\s*)?[\"(]',code),'unpriced scalar/operator redefinition in phase source')
        for name,owner in pure_owners.items():
            if re.search(r'\b(?:op|pred|abbrev)\s+(?:\[[^]]*\]\s*)?'+re.escape(name)+r'\b',code):
                policy.require(path==owner,'unreviewed shadow helper binding: '+name)
        for name in re.findall(r'\bmodule\s+(?!type\b)(\w+)\b',code):
            if name in module_owners:policy.require(module_owners[name]==path,'unreviewed phase module binding: '+name)
    for name,(file,rhs) in ALIASES.items():
        actual=declaration((policy.BASE/file).read_text(),'type',name)
        policy.require(policy.compact(actual)==policy.compact('type '+name+'='+rhs+'.'),'phase type alias changed: '+name)
    results={};endpoints=[]
    external=semantic_support(data)
    for endpoint,record in indexed.items():
        text=sources[endpoint]
        raw=declaration(text,'op',endpoint[3:]) if endpoint.startswith('op.') else cal.raw_body(text,endpoint)
        policy.require(policy.compact(raw)==policy.compact(record.get('source_fragment','')),'phase metadata source fragment drift: '+endpoint)
        policy.require(policy.sha(' '.join(policy.without_comments(raw).split()).encode())==record.get('normalized_body_sha256'),'phase body digest mismatch: '+endpoint)
        if endpoint.startswith('op.'):
            policy.require(policy.compact(raw)==policy.compact(OPS[endpoint[3:]]),'unexpanded/changed phase pure operation: '+endpoint)
        elif endpoint not in WRAPPERS and endpoint!='SimEncrypt.run':
            results[endpoint]=numeric_entry(text,endpoint,record)
        if endpoint in CRITICAL_BODIES:
            policy.require(manual.normalize(raw)==policy.compact(CRITICAL_BODIES[endpoint]),'critical phase semantics/control drift: '+endpoint)
        endpoints.append(INVENTORY[endpoint]+':'+endpoint)
    wrapper_costs=wrapper_entries(sources,indexed)
    bridges,forwarding=protocol_bridges(sources,results)
    prices=aggregate(data,results,wrapper_costs)
    return {'status':'PHASE_SOURCE_FEES_RECONSTRUCTED','endpoints':endpoints+bridges,
            'closed_prices':prices,'external_inputs':external,'source_blocks':results,'wrapper_boundaries':wrapper_costs,
            'actual_forwarding_blocks':forwarding,
            'metadata_status':data.get('status'),'inventory_entries':len(indexed),
            'scope':'Owned fixed arrays, persistent lists, unit integer control, explicit ideal ROM; ledger observations erased.'}



if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--draft',action='store_true')
    args=parser.parse_args();print(json.dumps(check(require_complete=not args.draft),indent=2))
