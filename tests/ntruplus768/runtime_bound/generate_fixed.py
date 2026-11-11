from pathlib import Path
import re, json, argparse, hashlib
ROOT=None; OUT=None
# The emitter only handles the extracted straight-line/while/if syntax used here.
# It is not a trusted proof producer: every projection and loop bound is checked.
def balanced(s,i,op='{',cl='}'):
 assert s[i]==op
 dep=1;j=i+1
 while dep:
  if s[j]==op:dep+=1
  if s[j]==cl:dep-=1
  j+=1
 return s[i+1:j-1],j

def parse_seq(s):
 out=[];i=0
 while i<len(s):
  if s[i].isspace():i+=1;continue
  if s.startswith('while',i) or s.startswith('if',i):
   kind='while' if s.startswith('while',i) else 'if';k=s.index('{',i)
   cond=s[i+len(kind):k].strip();body,j=balanced(s,k)
   node={'kind':kind,'cond':cond,'body':parse_seq(body)};i=j
   if kind=='if':
    while i<len(s) and s[i].isspace():i+=1
    node['else']=[]
    if s.startswith('else',i):
     k=s.index('{',i);other,i=balanced(s,k);node['else']=parse_seq(other)
   out.append(node);continue
  j=s.index(';',i)+1;line=' '.join(s[i:j].split());i=j
  if line.startswith('return '):out.append({'kind':'return','expr':line[7:-1]})
  elif '<@' in line:
   lhs,rhs=line[:-1].split('<@');m=re.match(r'([\w.]+)\s*(.*)',rhs.strip());out.append({'kind':'call','lhs':lhs.strip(),'target':m[1],'args':m[2]})
  else:
   assert '<-' in line,line
   out.append({'kind':'assign','line':line})
 return out

def array_cells(ty):
 return sum(map(int,re.findall(r"Array(\d+)\.t",ty)))

def expr_fee(expr):
 expr=expr.replace('<-','').replace('=>','')
 return len(re.findall(r'`(?:[^`]+)`|\\(?:ult|ule|slt|sle)|%/|%%|[+*<>=!]|(?<![<])-|\.\[|(?:sigextu\d+|zeroextu\d+|truncateu\d+|SHR_\d+)',expr))+2*expr.count('?')

def strip_outer_parens(expr):
 expr=expr.strip()
 while expr.startswith('('):
  inside,end=balanced(expr,0,'(',')')
  if end!=len(expr):break
  expr=inside.strip()
 return expr

def check_single_comparison_guard(cond,kind):
 # A guard's fixed fee 2 covers exactly one scalar comparison and one
 # branch.  Literal word construction (including a literal quotient) is
 # compile-time notation; <> is one comparison, not two runtime operators.
 # In particular, do not use the general expression allowlist to admit
 # array/list equality, function application or compound/arithmetic guards.
 expr=strip_outer_parens(cond)
 match=re.fullmatch(r'(\w+)\s*(\\(?:ult|ule|slt|sle)|<>|<=|>=|=|<|>)\s*(.+)',expr)
 assert match,('unsupported compound guard',cond)
 lhs,comparison,rhs=match.groups();rhs=strip_outer_parens(rhs)
 lhs_type=VARTYPES.get(lhs,'').strip()
 if lhs_type=='int':
  # The sole integer guard supported by the loop proof emitter is its
  # fixed-bound loop index; no unbounded integer input comparison is added.
  assert kind=='while' and comparison=='<' and re.fullmatch(r'\d+',rhs),('unsupported integer guard',cond)
  assert 0<=int(rhs)<=2048,('unsupported integer guard bound',cond)
  return
 word=re.fullmatch(r'W(8|16|32|64)\.t',lhs_type)
 assert word,('non-scalar guard operand',lhs,lhs_type,cond)
 if re.fullmatch(r'\w+',rhs):
  assert VARTYPES.get(rhs,'').strip()==lhs_type,('non-scalar or mismatched guard operand',rhs,cond)
  return
 literal=re.fullmatch(r'W(8|16|32|64)\.of_int\s+(.+)',rhs)
 assert literal and literal[1]==word[1],('unsupported guard operand expression',rhs,cond)
 value=strip_outer_parens(literal[2])
 assert re.fullmatch(r'\d+(?:\s*%/\s*\d+)?',value),('nonconstant guard operand',value,cond)
 terms=[int(x.strip()) for x in value.split('%/')]
 assert len(terms)==1 or terms[1]>0,('invalid literal guard quotient',cond)
 constant=terms[0] if len(terms)==1 else terms[0]//terms[1]
 assert 0<=constant<2**int(word[1]),('out-of-range literal guard operand',cond)

def charge(line):
 # An assignment contributes one transfer plus the syntax-visible primitive
 # arithmetic/logic/cast/address/load/store operations. Representation casts
 # W*.to_uint/of_int are semantic word/integer coercions, not instructions.
 lhs=line.split('<-')[0].strip()
 n=1+lhs.count(',')+expr_fee(line)
 if lhs in VARTYPES and '<- witness' not in line:n+=3*array_cells(VARTYPES[lhs])
 # Constants are installed by finite cell copying, not a unit-cost array op.
 m=re.search(r'Array(\d+)\.init',line)
 if m:n+=5*int(m[1])
 # Fresh scratch allocations reserve each cell explicitly.
 if '<- witness' in line:
  lhs=line.split('<-')[0].strip(); t=VARTYPES.get(lhs,'')
  m=re.search(r'Array(\d+)\.t',t)
  if m:n+=int(m[1])
 return n

FILES={
'PolySub':'poly_sub/extracted/NTRUPlus768PolySub.ec',
'DecapR2':'decap_r2_comp/extracted/NTRUPlus768DecapR2Comp.ec',
'SOTPEncode':'poly_sotp_encode_checked/extracted/NTRUPlus768PolySOTPEncodeChecked.ec',
'GPrepare':'decap_message/extracted/NTRUPlus768DecapMessagePrepare.ec',
'ToBytes':'poly_tobytes/extracted/NTRUPlus768PolyToBytes.ec',
'FromBytes':'poly_frombytes_checked/extracted/NTRUPlus768PolyFromBytesChecked.ec',
'CenteredAdd':'poly_centered_add_checked/extracted/NTRUPlus768PolyCenteredAdd.ec',
'NTT':'ntt/extracted/NTRUPlus768NTT.ec',
'InvNTT':'invntt/extracted/NTRUPlus768InvNTT.ec',
'Basemul':'poly_basemul/extracted/NTRUPlus768PolyBasemul.ec',
'Baseinv':'poly_baseinv_jasmin/extracted/NTRUPlus768PolyBaseInv.ec',
'CBD':'poly_cbd1_checked/extracted/NTRUPlus768PolyCBD1Checked.ec',
}
parser=argparse.ArgumentParser(description='Generate and audit the finite native-kernel cost instrumentation.')
parser.add_argument('name',choices=sorted(FILES));parser.add_argument('--root',type=Path,required=True)
parser.add_argument('--output-dir',type=Path,required=True);parser.add_argument('--manifest',type=Path)
a=parser.parse_args();name=a.name;checkout=a.root.resolve();ROOT=checkout/'ntruplus/proof/768/ref';OUT=a.output_dir.resolve();OUT.mkdir(parents=True,exist_ok=True)
src=ROOT/FILES[name];text=src.read_text();original=src.stem;mod='RTFixed'+name
before=text[:text.index('module M =')]
procs=[];pos=text.index('module M =')
while True:
 m=re.search(r'\bproc\s+(\w+)\s*\(',text[pos:])
 if not m:break
 start=pos+m.start(); pname=m[1];args,p=balanced(text,text.index('(',start),'(',')');k=text.index('= {',p)
 rett=text[p:k].strip().removeprefix(':').strip();body,end=balanced(text,k+2);sourcebody=body;pos=end
 decl=[]
 while (vm:=re.match(r'\s*var\s+(\w+)\s*:\s*(.*?);',body,re.S)):
  decl.append((vm[1],vm[2].strip()));body=body[vm.end():]
 params=[]
 for part in args.split(','):
  nm,ty=part.strip().split(':',1);params.append((nm,ty))
 procs.append({'name':pname,'args':args,'params':params,'ret':rett,'decl':decl,'nodes':parse_seq(body),'source_body_sha256':hashlib.sha256(sourcebody.encode()).hexdigest()})
byname={p['name']:p for p in procs}
def check_expr(expr,variables):
 known=set(variables)|{'true','false','witness','fun','i','i_0','init_msf','nTRUPLUS_ZETAS96','product__NTRUPLUS_ZETAS96','ult','ule','slt','sle'}
 for token in re.findall(r'[A-Za-z_][A-Za-z_0-9.]*(?<!\.)',expr):
  assert token in known or re.fullmatch(r'W\d+\.(of_int|to_uint)|Array(?:4|96|768)\.init|(?:sigextu|truncateu|zeroextu)\d+|SHR_\d+',token),('unsupported expression identifier',token,expr)
 assert all(op in ['<<','>>','|>>','&','|','^'] for op in re.findall(r'`([^`]+)`',expr)),('unsupported word operator',expr)
 assert not any(t in re.sub(r'`[^`]+`','',expr) for t in ['forall','exists','choice','oget','%r','**','^']),('unsupported expression',expr)
 if '.init' in expr:
  assert re.search(r'Array(?:4|96|768)\.init \(fun (?:i|i_0) => (?:tr|transformed|difference|nTRUPLUS_ZETAS96|product__NTRUPLUS_ZETAS96)\.\[\(0 \+ (?:i|i_0)\)\]\)',expr),('unsupported initializer',expr)
def check_nodes(nodes,variables):
 for n in nodes:
  if n['kind']=='assign':check_expr(n['line'],variables)
  if n['kind']=='call':
   assert n['target'] in byname,('unclosed call',n['target'])
   check_expr(n['args'],variables)
  if n['kind']=='return':check_expr(n['expr'],variables)
  if n['kind'] in ('if','while'):check_expr(n['cond'],variables);check_nodes(n['body'],variables)
  if 'else'in n:check_nodes(n['else'],variables)
for p in procs:check_nodes(p['nodes'],[x for x,_ in p['params']+p['decl']])

COSTS={}; allsource=[]
def callfee(nd):return 2+nd['args'].count(',')+1+expr_fee(nd['args'])+3*array_cells(byname[nd['target']]['ret'])

def setcost(nodes,prefix=0):
 cost=prefix
 for nd in nodes:
  nd['pre']=cost
  if nd['kind'] in ('if','while'):check_single_comparison_guard(nd['cond'],nd['kind'])
  if nd['kind']=='assign':nd['fee']=charge(nd['line']);cost+=nd['fee']
  elif nd['kind']=='call':nd['fee']=callfee(nd);cost+=nd['fee']+COSTS[nd['target']]
  elif nd['kind']=='return':nd['fee']=1+nd['expr'].count(',')+expr_fee(nd['expr'])+3*array_cells(CURRENT_RET);cost+=nd['fee']
  elif nd['kind']=='if':
   a=setcost(nd['body'],0);b=setcost(nd['else'],0);nd['fee']=2;cost+=2+max(a,b)
  else:
   cond=nd['cond'];mword=re.search(r'\((\w+)\s*\\ult',cond);nd['word']=mword is not None
   idx=(mword or re.search(r'\((\w+)\s*<',cond))[1];nd['idx']=idx
   if not nd['word']:
    nd['start']='0';nd['end']=re.search(r'<\s*(\d+)',cond)[1];nd['iterations']=int(nd['end'])
   elif 'stop' in cond:
    stops=[x['line'] for x in nodes if x['kind']=='assign' and x['line'].startswith('stop <-')]
    amount=int(re.search(r'of_int (\d+)',stops[-1])[1]);nd['start']='W64.to_uint base';nd['end']='W64.to_uint base+'+str(amount);nd['iterations']=amount
   else:
    expr=re.search(r'W64.of_int\s+(.+)\)\)',cond)[1].strip('() ')
    assert re.fullmatch(r'\d+(?:\s*%/\s*\d+)?',expr),('nonconstant loop bound',expr)
    terms=[int(x.strip())for x in expr.split('%/')];bound=terms[0] if len(terms)==1 else terms[0]//terms[1]
    assert 0<=bound<=2048,('unsupported fixed loop bound',bound)
    # The last literal assignment to the loop index before this loop.
    prior=nodes[:nodes.index(nd)];starts=[x['line'] for x in prior if x['kind']=='assign' and x['line'].startswith(idx+' <-')]
    st=int(re.search(r'of_int (\d+)',starts[-1])[1]);nd['start']=str(st);nd['end']=str(bound);nd['iterations']=bound-st
   body=setcost(nd['body'],0);nd['step']=body+2;cost+=2+nd['iterations']*nd['step'];nd['fee']=2
  nd['post']=cost
 return cost

def emit(nodes,indent='    '):
 out=[]
 for nd in nodes:
  k=nd['kind']
  if k=='assign':out += [indent+nd['line'],indent+f'rt_work <- rt_work + {nd["fee"]};']
  elif k=='call':
   t=nd['target'];out += [indent+f'rt_call_{t} <@ {t} {nd["args"]};',indent+f'{nd["lhs"]} <- rt_call_{t}.`1;',indent+f'rt_work <- rt_work + rt_call_{t}.`2 + {nd["fee"]};']
  elif k=='return':out += [indent+f'rt_work <- rt_work + {nd["fee"]};',indent+f'return ({nd["expr"]},rt_work);']
  elif k=='if':out += [indent+'rt_work <- rt_work + 2;',indent+'if '+nd['cond']+' {',*emit(nd['body'],indent+'  '),indent+'} else {',*emit(nd['else'],indent+'  '),indent+'}']
  else:out += [indent+'rt_work <- rt_work + 2;',indent+'while '+nd['cond']+' {',*emit(nd['body'],indent+'  '),indent+'  rt_work <- rt_work + 2;',indent+'}']
 return out

def gather(nodes,kind):
 r=[]
 for nd in nodes:
  if nd['kind']==kind:r.append(nd)
  if 'body'in nd:r+=gather(nd['body'],kind)
  if 'else'in nd:r+=gather(nd['else'],kind)
 return r

def proof_projection(nodes,p,indent=' '):
 r=[]
 for nd in reversed(nodes):
  k=nd['kind']
  if k=='call':r.append(indent+f'wp;call rt_fixed_{name.lower()}_{nd["target"]}_projection.')
  elif k=='if':
   r.append(indent+'wp;if.');r+=[' '+indent+'+ '+x.strip() if j==0 else ' '+indent+'  '+x.strip() for j,x in enumerate(proof_projection(nd['body'],p))]
   r+=proof_projection(nd['else'],p,indent+' ')
  elif k=='while':
   live=[x for x,_ in p['params']]+[nd['idx']]
   for rn in gather(p['nodes'],'return'):
    live += [x for x in re.findall(r'\b[A-Za-z_]\w*',rn['expr']) if x in dict(p['decl'])]
   if 'stop' in nd['cond']:live+=['stop']
   if not nd.get('word',True):live += [v for v in ['transformed','difference'] if v in dict(p['decl'])]
   if 'zetasp' in dict(p['decl']):live+=['zetasp']
   live += [v for v in ['ta','tb','tr'] if v in dict(p['decl'])]
   if 'status' in dict(p['decl']):live+=['status']
   r.append(indent+'wp;while(={'+','.join(dict.fromkeys(live))+'}).')
   r+=[' '+indent+'+ '+x.strip() if j==0 else ' '+indent+'  '+x.strip() for j,x in enumerate(proof_projection(nd['body'],p))]
 r.append(indent+'auto.')
 return r

def proof_cost_straight(nodes,indent=' ',loopbody=False):
 r=[]
 for nd in reversed(nodes):
  if nd['kind']=='call':r.append(indent+f'wp;call rt_fixed_{name.lower()}_{nd["target"]}_cost.')
  elif nd['kind']=='if':
   r.append(indent+'wp;if.');r+=[' '+indent+'+ '+x.strip() if j==0 else ' '+indent+'  '+x.strip() for j,x in enumerate(proof_cost_straight(nd['body'],loopbody=loopbody))];r+=proof_cost_straight(nd['else'],indent+' ',loopbody)
  elif nd['kind']=='while':
   idx=nd['idx'];start=nd['start'];end=nd['end'];lo='0' if start=='0' else start
   val='W64.to_uint '+idx if nd['word'] else idx
   inv=f'{lo}<={val}<={end} /\\ 0<=rt_work<={nd["pre"]+2}+{nd["step"]}*({val}-({start}))'
   if 'stop' in nd['cond']:inv+=' /\\ 0<=W64.to_uint base<=768 /\\ W64.to_uint stop='+end
   r.append(indent+'wp;while('+inv+').')
   r+=[' '+indent+'+ '+x.strip() if j==0 else ' '+indent+'  '+x.strip() for j,x in enumerate(proof_cost_straight(nd['body'],loopbody=nd['word']))]
 if not loopbody and any(n['kind']=='while' and 'stop' in n['cond'] for n in nodes):
  amount=next(n['iterations'] for n in nodes if n['kind']=='while' and 'stop' in n['cond'])
  r.append(indent+'auto=> /> &hr hb0 hb1.')
  r.append(indent+f'have hs:W64.to_uint(base{{hr}}+W64.of_int {amount})=W64.to_uint base{{hr}}+{amount}.')
  r.append(indent+'+ apply rt_fixed_u64_add;smt().')
  r.append(indent+'smt(W64.ultE).')
 else:r.append(indent+('auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().' if loopbody else 'auto=> />;smt(rt_fixed_exit).'))
 return r

out=[before,'require import '+original+'.','(* Each rt_work update is a ghost charge for the preceding concrete instruction.\n   Each array parameter is copied into an owned buffer (3N primitive events: allocation, load, store). Whole-array assignments/returns also pay 3N; Array.set updates this owned buffer. These procedures preserve the original data path; no global state is added. *)',f'module {mod} = {{']
for p in procs:
 VARTYPES=dict(p['decl']+p['params']);CURRENT_RET=p['ret'];p['entry']=3*sum(array_cells(t) for _,t in p['params']);p['cost']=setcost(p['nodes'],p['entry']);COSTS[p['name']]=p['cost']
 out += [f'  proc {p["name"]} ({p["args"]}) : ({p["ret"]}) * int = {{','    var rt_work:int;']
 out += [f'    var {nm}:{ty};'for nm,ty in p['decl']]
 for c in sorted({n['target'] for n in gather(p['nodes'],'call')}):out += [f'    var rt_call_{c}:({byname[c]["ret"]}) * int;']
 out+=[f'    rt_work <- {p["entry"]};',*emit(p['nodes']),'  }']
out+=['}.','', 'lemma rt_fixed_u64_next (i:W64.t) : W64.to_uint i<2048 => W64.to_uint(i+W64.one)=W64.to_uint i+1.', 'proof. move=>h;rewrite W64.to_uintD_small /=;smt(W64.to_uint_cmp). qed.', 'lemma rt_fixed_u64_add (i:W64.t)(n:int) : 0<=W64.to_uint i<=768 => 0<=n<=768 => W64.to_uint(i+W64.of_int n)=W64.to_uint i+n.', 'proof. move=>hi hn;have hnE:W64.to_uint(W64.of_int n)=n. + rewrite W64.to_uint_small;smt(). rewrite W64.to_uintD_small. + rewrite hnE;smt(). by rewrite hnE. qed.', 'lemma rt_fixed_ult (i:W64.t)(n:int) : 0<=n<2048 => (i \\ult W64.of_int n)=(W64.to_uint i<n).', 'proof. move=>hn;rewrite W64.ultE W64.to_uint_small;smt(). qed.', 'lemma rt_fixed_exit (i:W64.t)(n:int) : 0<=n<2048 => !(i \\ult W64.of_int n) => W64.to_uint i<=n => W64.to_uint i=n.', 'proof. move=>hn;rewrite(rt_fixed_ult i n hn);smt(). qed.', '']
for p in procs:
 pn=p['name'];pre='0<=W64.to_uint base<=768' if 'base' in dict(p['params']) else 'true'
 out += [f'lemma rt_fixed_{name.lower()}_{pn}_projection :',f' equiv[{mod}.{pn} ~ {original}.M.{pn} :', ' ={'+','.join(x for x,_ in p['params'])+'} ==> res{1}.`1=res{2}].','proof. proc.',*proof_projection(p['nodes'],p),'qed.']
 if True:
  out += [f'lemma rt_fixed_{name.lower()}_{pn}_cost :',f' hoare[{mod}.{pn} : {pre} ==> 0<=res.`2<={p["cost"]}].','proof. proc.',*proof_cost_straight(p['nodes']),'qed.']
 else:
  out += [f'(* COST LOOP {pn}: {p["cost"]} *)']
top=procs[-1];pn=top['name'];bname='rt_fixed_'+name.lower()+'_bound'
out += [f'op {bname}:int = {top["cost"]}.',f'lemma {bname}_cost : hoare[{mod}.{pn} : true ==>0<=res.`2<={bname}].',f'proof. exact rt_fixed_{name.lower()}_{pn}_cost. qed.']
rendered='\n'.join(out)+'\n'
if name=='Baseinv':
 overrides=json.loads((Path(__file__).parent/'baseinv-proof-overrides.json').read_text())
 for lemma,proof in overrides.items():
  pattern=r'(lemma rt_fixed_baseinv_'+re.escape(lemma)+r'\s*:.*?\n)proof\..*?\nqed\.'
  rendered,n=re.subn(pattern,lambda m:m[1]+'proof. '+proof+'\nqed.',rendered,flags=re.S)
  assert n==1,(lemma,n)
(OUT/f'NTRUPlus768RTFixed{name}.ec').write_text(rendered)
def proc_bodies(source):
 result={};pos=source.index('module '+mod+' =')
 while (m:=re.search(r'\bproc\s+(\w+)\s*\(',source[pos:])):
  start=pos+m.start();k=source.index('= {',start);body,pos=balanced(source,k+2);result[m[1]]=hashlib.sha256(body.encode()).hexdigest()
 return result
measured=proc_bodies(rendered)
record={'name':name,'source':str(src.relative_to(checkout)),'source_sha256':hashlib.sha256(text.encode()).hexdigest(),
 'generated_source':str(Path('ntruplus/proof/768/ref/kem_runtime_bound')/f'NTRUPlus768RTFixed{name}.ec'),
 'generated_source_sha256':hashlib.sha256(rendered.encode()).hexdigest(),
 'procedures':[{'source_name':original+'.M.'+p['name'],'generated_name':mod+'.'+p['name'],
  'source_body_sha256':p['source_body_sha256'],'generated_body_sha256':measured[p['name']],
  'projection':f'rt_fixed_{name.lower()}_{p["name"]}_projection','cost_lemma':f'rt_fixed_{name.lower()}_{p["name"]}_cost',
  'cost':p['cost'],'entry_array_copy_fee':p['entry'],'ast':p['nodes']} for p in procs]}
if a.manifest:a.manifest.parent.mkdir(parents=True,exist_ok=True);a.manifest.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'group':name,'procedures':len(procs),'top_cost':top['cost']}))
