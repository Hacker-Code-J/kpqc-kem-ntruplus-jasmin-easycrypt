"""Executable-path and resource-scope guards, supplementary to kernel checking."""
import importlib.util
import re
import policy

_path = policy.TEST.parent / 'history_refinement/executable_policy.py'
_spec = importlib.util.spec_from_file_location('runtime_ec_syntax', _path)
syntax = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(syntax)

ORDERED = {
 'RTOracles': ['op rt_raw_g_exec', 'size input=1153', 'nth W8.zero input 0=W8.one',
  'S.charge_call(rt_raw_g_exec input outlen,size input);',
  'out<@AHOracles(S,O).raw(input,outlen);', 'module RTDecap',
  'S.charge_call(false,0);st<@S.snapshot();',
  'out<@HistLookup(AHPublicG(O)).run', 'S.charge_decap(out.`2,out.`3,out.`4);'],
 'RTAdaptive': ['p.`rp_h+p.`rp_d+p.`rp_g<=p.`rp_q', 'size queries=rt_g_length p',
  'module RTTranscript', 'SecGHistory.init();key<$uniform32;',
  'ignored<@RTActualPhase(S,A,SecGLogged(FOGActual)).run(pk,ct,key);',
  'profile<@S.metrics();return(SecGHistory.queries,profile);', 'lemma rt_adversary_invariant',
  'lemma rt_transcript_bound'],
 'RTStore': ['updated<@HistTable.put(input,hout,st.`ah_rows);',
  'p<-rt_record p updated.`2 updated.`3;'],
 'RTView': ['lemma rt_transcript_projection', 'res{1}.`1=res{2}',
  'view(glob S){1}=view(glob S){2}'],
}
MUTATIONS = [
 ('RTOracles','raw-zero-not-counted','S.charge_call(rt_raw_g_exec input outlen,size input);','S.charge_call(false,0);'),
 ('RTOracles','hidden-existential-execution','S.charge_call(rt_raw_g_exec input outlen,size input);','S.charge_call(rt_raw_g input outlen,size input);'),
 ('RTOracles','lookup-charge-omission','S.charge_decap(out.`2,out.`3,out.`4);',''),
 ('RTAdaptive','callback-budget-lost','p.`rp_h+p.`rp_d+p.`rp_g<=p.`rp_q','p.`rp_g<=p.`rp_q'),
 ('RTStore','unmeasured-history-put','updated<@HistTable.put(input,hout,st.`ah_rows);','updated<-(hist_put input hout st.`ah_rows,0,0);'),
]
GHOST_GAMES = {('RTWordGames','RTWordNTRURealGame'),
 ('RTWordGames','RTWordNTRUUniformGame'),('RTWordGames','RTWordRLWEGame'),
 ('RTWordGames','RTPolyNTRUAdapter'),('RTWordGames','RTPolyRLWEAdapter')}
NONCONSTRUCTIVE = re.compile(r'\b(?:exists|forall|choiceb?|ofassoc|fdom|fsize|elems)\b')
POLYNOMIAL = re.compile(r'\b(?:input_poly|ow_coeff_words|ow_key_poly|ow_rlwe_value|NTRUPoly|pke_rq_unit)\b')


def current_sources():
    return {p.stem.removeprefix('NTRUPlus768'): p.read_text() for p in policy.PROOF.glob('*.ec')}


def executable_operations(sources):
    """Follow local pure helpers called by programs, so a renamed wrapper cannot hide choice."""
    operations = {}
    for text in sources.values():
        code = policy.without_comments(text)
        for match in re.finditer(r'(?ms)^\s*(?:op|abbrev|pred)\s+(?:\[[^]]*\]\s*)?(\w+)\b(.*?)(?<!\.)\.\s*(?=\n|$)', code):
            declaration = match.group(2)
            equal = re.search(r'(?<![<>=])=(?![=>])', declaration)
            if equal:
                operations[match.group(1)] = operations.get(match.group(1),'')+' '+declaration[equal.end():]
    return operations


def check_executable(body, operations, *, word=False, header=''):
    policy.require(not NONCONSTRUCTIVE.search(body), 'nonconstructive operation in executable body')
    if word:
        policy.require(not POLYNOMIAL.search(header + body), 'polynomial reification in word backend')
    seen = set()
    pending = set(re.findall(r'\b\w+\b', body)) & set(operations)
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        expression = operations[name]
        policy.require(not NONCONSTRUCTIVE.search(expression), 'nonconstructive helper reachable from executable: ' + name)
        if word:
            policy.require(not POLYNOMIAL.search(expression), 'word backend calls polynomial helper: ' + name)
        pending.update((set(re.findall(r'\b\w+\b', expression)) & set(operations)) - seen)
    return sorted(seen)


def word_closure(sources,operations):
    modules={};aliases={}
    for source,text in sources.items():
        for module,block in syntax.modules(text):
            policy.require(module not in modules,'ambiguous runtime module name')
            modules[module]=(source,syntax.procedures(block))
        for match in re.finditer(r'(?m)^\s*(?:local\s+)?module\s+(?!type\b)(\w+)[^\n=]*=([^\n]+)\.\s*$',policy.without_comments(text)):
            if not match.group(2).lstrip().startswith('{'):aliases[match.group(1)]=match.group(2)
    pending=[m for m,(source,_) in modules.items() if m.startswith('RTWord') and (source,m) not in GHOST_GAMES]
    seen=set()
    while pending:
        module=pending.pop()
        if module in seen:continue
        seen.add(module)
        if module in aliases:
            pending.extend(set(re.findall(r'\b\w+\b',aliases[module]))&(set(modules)|set(aliases)))
        if module not in modules:continue
        source,procedures=modules[module]
        policy.require((source,module) not in GHOST_GAMES,'word program calls a mathematical challenger bridge')
        for name,header,body,_i,_j in procedures:
            check_executable(body,operations,word=True,header=header)
            pending.extend(set(re.findall(r'\b\w+\b',body))&(set(modules)|set(aliases)))
    return sorted(seen)


def check(sources=None, *, require_complete=True, reviewed_manifest=None):
    sources = current_sources() if sources is None else sources
    policy.require(sources and all(re.fullmatch(r'RT[A-Za-z0-9_]+', key) for key in sources), 'unreviewed runtime source family')
    operations = executable_operations(sources)
    records = []
    reachable=word_closure(sources,operations)
    for name, text in sources.items():
        policy.check_proof_text(text)
        policy.require(re.search(r'\blemma\s+\w+', policy.without_comments(text)), 'runtime source has no semantic theorem')
        if name in ORDERED:
            policy.shared.ordered(policy.compact(text), ORDERED[name])
        for module, block in syntax.modules(text):
            rest=block
            for _name,_header,_body,begin,end in reversed(syntax.procedures(block)):
                rest=rest[:begin]+rest[end:]
            if re.search(r'\bvar\b',rest):
                policy.require((name,module)==('RTFinal','RTPrivateStore'),'new public/global state outside fresh private store')
                policy.require(policy.compact(rest)==policy.compact('var st:ah_state var ledger:rt_profile'),'private state layout changed')
            word = module.startswith('RTWord') and (name,module) not in GHOST_GAMES
            for proc, header, body, _begin, _end in syntax.procedures(block):
                # Mathematical interface reducers and proof-only game bridges
                # remain distinct from the word-array execution endpoints.
                helpers = check_executable(body, operations, word=word, header=header) if word else []
                if name == 'RTOracles':
                    helpers = check_executable(body, operations)
                records.append({'source':name,'module':module,'procedure':proc,
                    'scope':'word-executable' if word else 'ghost-hardness-interface' if (name,module) in GHOST_GAMES else 'reviewed-model-or-program', 'local_helpers':helpers})
    if 'RTFinal' in sources:
        code = policy.without_comments(sources['RTFinal'])
        declarations=list(re.finditer(r'\bdeclare\s+module\s+A\s*<:\s*CCAExtendedAdversary\s*(\{[^}]*\})',code))
        stores=list(re.finditer(r'\blocal\s+module\s+RTPrivateStore\s*:\s*RTHistory',code))
        policy.require(len(declarations)==len(stores)==1,'final needs exactly one original A and fresh store')
        declared,store=declarations[0],stores[0]
        import scope_controls
        policy.require(declared and store and declared.end() < store.start(), 'private runtime store must be local and fresh after A')
        policy.require(policy.compact(declared.group(1)) == scope_controls.original_adversary_restriction(), 'final changes original A restrictions')
    import calibration_policy
    calibration = calibration_policy.check(require_complete=require_complete, reviewed_manifest=reviewed_manifest)
    return {'procedures': records, 'word_call_closure':reachable, 'calibration': calibration,
            'scope':'Unit-cost integer/word operations and ideal-ROM primitives; not native CPU, bit complexity, CT/SCT, or a general PPT theorem.'}
