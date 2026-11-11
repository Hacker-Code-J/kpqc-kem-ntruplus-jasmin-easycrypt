"""Independent closed-fragment parser and source fee reconstruction.

This implementation consumes original procedure text; it does not trust the
instrumentation generator's AST, node fees, loop counts or total bound.
"""
import re
import policy
import calibration_policy as calibration


def cells(type_text):
    return sum(int(n) for n in re.findall(r'Array(\d+)\.t',type_text))


def validate_type(text):
    flat=text.replace('(','').replace(')','').strip()
    atoms=[x.strip() for x in flat.split('*')]
    policy.require(atoms and all(atoms),'empty native type')
    for atom in atoms:
        if atom in ('int','bool'):continue
        match=re.fullmatch(r'W(8|16|32|64)\.t(?:\s+Array(\d+)\.t)?',atom)
        policy.require(match,'unsupported native scalar/array type: '+atom)
        policy.require(match.group(2) is None or 0<int(match.group(2))<=2048,'unreviewed native array shape')


def closing(text,start,left='(',right=')'):
    policy.require(text[start]==left,'expected opening delimiter')
    depth=0
    for i in range(start,len(text)):
        if text[i]==left:depth+=1
        elif text[i]==right:
            depth-=1
            if not depth:return i
    raise ValueError('unclosed source delimiter')


def statements(text):
    result=[];i=0
    while i<len(text):
        if text[i].isspace():i+=1;continue
        kind=next((k for k in ('while','if') if re.match(k+r'\b',text[i:])),None)
        if kind:
            opening=text.index('{',i);end=closing(text,opening,'{','}')
            node={'kind':kind,'cond':text[i+len(kind):opening].strip(),
                  'body':statements(text[opening+1:end])};i=end+1
            if kind=='if':
                while i<len(text) and text[i].isspace():i+=1
                node['else']=[]
                if re.match(r'else\b',text[i:]):
                    opening=text.index('{',i);end=closing(text,opening,'{','}')
                    node['else']=statements(text[opening+1:end]);i=end+1
            result.append(node);continue
        semi=text.find(';',i);policy.require(semi>=0,'unterminated source statement')
        statement=text[i:semi+1].strip();i=semi+1
        if statement.startswith('return '):node={'kind':'return','expr':statement[7:-1].strip()}
        elif '<@' in statement:
            lhs,rhs=statement[:-1].split('<@',1);call=re.fullmatch(r'\s*([\w.]+)\s*(\(.*\))\s*',rhs,re.S)
            policy.require(call,'unsupported native call syntax')
            node={'kind':'call','lhs':lhs.strip(),'target':call.group(1),'args':call.group(2)}
        else:
            policy.require(statement.count('<-')==1 and '<$' not in statement,'unsupported native statement')
            node={'kind':'assign','line':statement}
        result.append(node)
    return result


def source_procedure(text,qualified):
    proc=qualified.split('.')[-1];code=calibration.code_mask(text)
    found=list(re.finditer(r'\bproc\s+'+re.escape(proc)+r'\s*\(',code));policy.require(len(found)==1,'ambiguous native procedure')
    opening=code.index('(',found[0].start());end=closing(code,opening)
    args=text[opening+1:end];body_open=code.index('{',end)
    ret=text[end+1:body_open].strip().removeprefix(':').strip()
    policy.require(ret.endswith('='),'unsupported return declaration');ret=ret[:-1].strip()
    types={}
    for part in args.split(','):
        if not part.strip():continue
        name,ty=part.split(':',1);policy.require(re.fullmatch(r'\s*\w+\s*',name),'unsupported parameter declaration');types[name.strip()]=ty.strip()
    params=dict(types);raw=calibration.raw_body(text,qualified)
    while True:
        decl=re.match(r'\s*var\s+(\w+)\s*:\s*([^;]+);',raw)
        if not decl:break
        types[decl.group(1)]=decl.group(2).strip();raw=raw[decl.end():]
    for ty in [*types.values(),ret]:validate_type(ty)
    return {'params':params,'types':types,'return':ret,'nodes':statements(raw)}


def expression_fee(expression,variables):
    policy.require(isinstance(variables,dict),'native expression requires a typed environment')
    for ty in variables.values():validate_type(ty)
    policy.require('::' not in expression,'list construction outside native fragment')
    known=set(variables)|{'true','false','witness','fun','i','i_0','init_msf','nTRUPLUS_ZETAS96','product__NTRUPLUS_ZETAS96'}
    original=expression
    expression=expression.replace('<-','').replace('=>','')
    bitops=re.findall(r'`([^`]+)`',expression)
    policy.require(all(x in {'<<','>>','|>>','&','|','^'} for x in bitops),'unsupported bit operator')
    rest=re.sub(r'`[^`]+`',' OP ',expression)
    rest=re.sub(r'\\(?:ult|ule|slt|sle)',' OP ',rest)
    tokens=re.findall(r'[A-Za-z_][A-Za-z_0-9.]*(?<!\.)',rest)
    for token in tokens:
        policy.require(token=='OP' or token in known or re.fullmatch(r'W\d+\.(?:of_int|to_uint)|Array(?:4|96|768)\.init|(?:sigextu|truncateu|zeroextu)\d+|SHR_\d+',token),'unsupported source expression identifier: '+token)
    residue=re.sub(r'[A-Za-z_][A-Za-z_0-9.]*(?<!\.)','',rest)
    residue=residue.replace('%/','').replace('%%','')
    policy.require(not re.search(r'[^\s\d()+*<>=!\-.,\[\];?:]',residue),'unsupported source expression token')
    policy.require('**' not in expression,'unsupported exponentiation')
    if '.init' in expression:
        policy.require(re.search(r'Array(?:4|96|768)\.init\s*\(fun (?:i|i_0)\s*=>\s*(?:tr|transformed|difference|nTRUPLUS_ZETAS96|product__NTRUPLUS_ZETAS96)\.\[\(0 \+ (?:i|i_0)\)\]\)',original),'unpriced array initializer')
    # A scalar transfer is accounted by its surrounding assignment/call.
    return len(re.findall(r'`[^`]+`|\\(?:ult|ule|slt|sle)|%/|%%|[+*<>=!]|(?<![<])-|\.\[|(?:sigextu\d+|zeroextu\d+|truncateu\d+|SHR_\d+)',expression))+2*expression.count('?')


def assignment_fee(line,types):
    lhs,rhs=line[:-1].split('<-',1);lhs=lhs.strip()
    if lhs.startswith('('):
        names=[x.strip() for x in lhs.strip('() ').split(',')]
        policy.require(all(n in types and cells(types[n])==0 for n in names),'array/unknown tuple assignment is not calibrated')
        policy.require(re.match(r'\s*\(?\s*SHR_(?:16|32|64)\b',rhs),'only scalar SHR multi-result assignment is calibrated')
    fee=1+lhs.count(',')+expression_fee(line,types)
    if lhs in types and 'witness' not in rhs:fee+=3*cells(types[lhs])
    init=re.search(r'Array(\d+)\.init',line)
    if init:fee+=5*int(init.group(1))
    if rhs.strip()=='witness':fee+=cells(types.get(lhs,''))
    return fee


def scalar_bound(expr):
    policy.require(re.fullmatch(r'\d+(?:%/\d+)?',expr),'nonconstant loop bound')
    parts=[int(x) for x in expr.split('%/')]
    value=parts[0] if len(parts)==1 else parts[0]//parts[1]
    policy.require(0<=value<=2048,'unsupported finite loop bound');return value


def single_scalar_guard(condition,kind,types):
    """A guard fee of two covers one scalar comparison, never an array or call."""
    compact=re.sub(r'[\s()]','',condition)
    m=re.fullmatch(r'(\w+)(\\(?:ult|ule|slt|sle)|<>|=|<|>)'
                   r'(\w+|W(?:8|16|32|64)\.of_int\d+(?:%/\d+)?)',compact)
    policy.require(m,'unpriced compound guard')
    lhs,operator,rhs=m.groups();ty=types.get(lhs)
    if ty=='int':
        policy.require(kind=='while' and operator=='<' and rhs.isdecimal(),'unreviewed integer guard')
        scalar_bound(rhs);return
    word=re.fullmatch(r'W(8|16|32|64)\.t',ty or '')
    policy.require(word,'non-scalar guard operand')
    literal=re.fullmatch(r'W'+word.group(1)+r'\.of_int(\d+(?:%/\d+)?)',rhs)
    policy.require(literal or types.get(rhs)==ty,'guard operand type or primitive shape mismatch')
    if literal:
        terms=[int(x) for x in literal.group(1).split('%/')]
        policy.require(len(terms)==1 or terms[1]!=0,'undefined constant guard quotient')


def inspect_nodes(nodes,declared,types,ret,callee_costs,callee_returns,start=0):
    policy.require(len(nodes)==len(declared),'statement coverage omission')
    cost=start
    for index,(node,meta) in enumerate(zip(nodes,declared)):
        kind=node['kind'];policy.require(meta.get('kind')==kind,'AST node kind drift')
        for key in ('line','cond','lhs','target','args','expr'):
            if key in node:policy.require(policy.compact(node[key])==policy.compact(meta.get(key,'')),'source statement/AST drift')
        policy.require(meta.get('pre')==cost,'AST prefix charge drift')
        if kind=='assign':fee=assignment_fee(node['line'],types);cost+=fee
        elif kind=='return':
            policy.require('.init' not in node['expr'] and 'witness' not in node['expr'],'unpriced allocation in native return')
            fee=1+node['expr'].count(',')+expression_fee(node['expr'],types)+3*cells(ret);cost+=fee
        elif kind=='call':
            target=node['target'];policy.require(target in callee_costs,'unclosed or recursive calibrated call')
            policy.require('.init' not in node['args'] and 'witness' not in node['args'],'unpriced allocation in native call argument')
            fee=3+node['args'].count(',')+expression_fee(node['args'],types)+3*cells(callee_returns[target]);cost+=fee+callee_costs[target]
        elif kind=='if':
            single_scalar_guard(node['cond'],kind,types)
            guard=re.sub(r'[\s()]','',node['cond'])
            policy.require(re.fullmatch(r'\w+(?:=|<>)W\d+\.of_int\d+',guard),'unpriced compound branch guard')
            a=inspect_nodes(node['body'],meta['body'],types,ret,callee_costs,callee_returns)
            b=inspect_nodes(node['else'],meta['else'],types,ret,callee_costs,callee_returns)
            fee=2;cost+=fee+max(a,b)
        elif kind=='while':
            single_scalar_guard(node['cond'],kind,types)
            guard=re.sub(r'[\s()]','',node['cond']);integer=re.fullmatch(r'(\w+)<(\d+)',guard)
            word=re.fullmatch(r'(\w+)\\ult(?:W64\.of_int(\d+(?:%/\d+)?)|(stop))',guard)
            policy.require(integer or word,'unpriced or non-fixed loop guard')
            idx=(integer or word).group(1)
            prior=[n['line'] for n in nodes[:index] if n['kind']=='assign']
            if integer:
                starts=[s for s in prior if re.match(re.escape(idx)+r'\s*<-',s)]
                policy.require(starts and re.sub(r'[\s()]','',starts[-1])==idx+'<-0;','unreviewed integer loop initializer')
                lo='0';hi=integer.group(2);iterations=int(hi)
            elif word.group(3):
                stops=[s for s in prior if re.match(r'\s*stop\s*<-',s)]
                policy.require(stops,'missing stop initializer')
                amount=re.search(r'W64\.of_int\s+(\d+)',stops[-1]);policy.require(amount,'unbounded stop')
                iterations=int(amount.group(1));lo='W64.to_uint base';hi=lo+'+'+str(iterations)
            else:
                upper=scalar_bound(word.group(2));starts=[s for s in prior if re.match(re.escape(idx)+r'\s*<-',s)]
                policy.require(starts,'missing loop index initializer')
                initial=re.search(r'W64\.of_int\s+(\d+)',starts[-1]);policy.require(initial,'unbounded loop start')
                lo=initial.group(1);hi=str(upper);iterations=upper-int(lo)
            policy.require(0<=iterations<=2048,'invalid loop iterations')
            policy.require(meta.get('idx')==idx and meta.get('word')==(word is not None) and meta.get('start')==lo and meta.get('end')==hi and meta.get('iterations')==iterations,'fixed loop metadata drift')
            inner=inspect_nodes(node['body'],meta['body'],types,ret,callee_costs,callee_returns)
            policy.require(meta.get('step')==inner+2,'loop step charge drift');fee=2;cost+=fee+iterations*(inner+2)
        else:raise ValueError('unsupported source statement kind')
        policy.require(meta.get('fee')==fee and meta.get('post')==cost,'source-derived fee or total was changed')
    return cost


def check_group(group):
    text=calibration.path(group['source']).read_text();costs={};returns={}
    inventory=re.findall(r'\bproc\s+(\w+)\s*\(',calibration.code_mask(text))
    policy.require(inventory==[x['source_name'].split('.')[-1] for x in group['procedures']], 'original procedure inventory omitted or reordered')
    for item in group['procedures']:
        proc=source_procedure(text,item['source_name']);name=item['source_name'].split('.')[-1]
        entry=3*sum(cells(ty) for ty in proc['params'].values())
        policy.require(item.get('entry_array_copy_fee')==entry,'entry clone charge drift')
        total=inspect_nodes(proc['nodes'],item['ast'],proc['types'],proc['return'],costs,returns,entry)
        policy.require(total==item['cost'],'calibrated theorem bound differs from actual source charges')
        costs[name]=total;returns[name]=proc['return']
    return {'group':group['name'],'procedures':len(costs),'result':'SOURCE_FEES_RECONSTRUCTED'}
