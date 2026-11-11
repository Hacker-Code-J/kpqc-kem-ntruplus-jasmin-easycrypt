"""Independent source-to-charge templates for manually instrumented word scans.

The templates follow the reviewed primitive convention, not the counters or
bounds read from the file under test. Resealing input hashes does not relax them.
"""
import re
import policy


def normalize(body):
    return policy.compact(re.sub(r'\bvar\s+[^;]+;', '', policy.without_comments(body)))


def expected_primitive(name):
    if name in ('suffix','cipher'):
        n=32 if name=='suffix' else 1152
        return f'''same<-true;comparisons<-0;work<-{6*n+2};work<-work+2;
 while(comparisons<{n}){{
 left_byte<-x.[comparisons];work<-work+2;right_byte<-y.[comparisons];work<-work+2;
 byte_equal<-(left_byte=right_byte);work<-work+2;same<-same /\\ byte_equal;work<-work+2;
 comparisons<-comparisons+1;work<-work+2;work<-work+2;}}
 work<-work+1;return(same,work);'''
    if name=='key':
        return '''same<-true;comparisons<-0;work<-770;work<-work+2;
 while(comparisons<128){work<-work+2;if(comparisons<96){
 left_byte<-x.`1.[comparisons];work<-work+2;right_byte<-y.`1.[comparisons];work<-work+2;
 }else{left_byte<-x.`2.[comparisons-96];work<-work+3;right_byte<-y.`2.[comparisons-96];work<-work+3;}
 byte_equal<-(left_byte=right_byte);work<-work+2;same<-same /\\ byte_equal;work<-work+2;
 comparisons<-comparisons+1;work<-work+2;work<-work+2;}work<-work+1;return(same,work);'''
    if name=='word_equal':
        return '''same<-true;i<-0;work<-4610;work<-work+2;while(i<768){
 word_equal<-(x.[i]=y.[i]);work<-work+4;same<-same /\\ word_equal;work<-work+2;
 i<-i+1;work<-work+2;work<-work+2;}work<-work+1;return(same,work);'''
    if name=='copy768':
        return '''out<-witness;work<-3073;i<-0;work<-work+1;work<-work+2;
 while(i<768){out.[i]<-x.[i];work<-work+3;i<-i+1;work<-work+2;work<-work+2;}
 work<-work+2305;return(out,work);'''
    raise ValueError('unsupported manual primitive: '+name)


def expected_scale():
    return '''steps<-0;steps<-steps+2304;i<-0;steps<-steps+1;steps<-steps+2;
 while(i<768){x<-3*W16.to_uint a.[i];steps<-steps+4;
 steps<-steps+2;if(3457<=x){x<-x-3457;steps<-steps+2;}
 steps<-steps+2;if(3457<=x){x<-x-3457;steps<-steps+2;}
 a.[i]<-W16.of_int x;steps<-steps+3;i<-i+1;steps<-steps+2;steps<-steps+2;}
 steps<-steps+2304;steps<-steps+1;return(a,steps);'''


def expected_wordcheck(name):
    if name=='normalize':
        return 'rt_work<-2304;output<-witness;rt_work<-rt_work+769;i<-0;rt_work<-rt_work+1;rt_work<-rt_work+2;\nwhile(i<768){x<-coeff ap.[i];rt_work<-rt_work+2;z<-x%%3457;rt_work<-rt_work+2;\nrt_work<-rt_work+2;if(1728<z){z<-z-3457;rt_work<-rt_work+2;}\noutput.[i]<-W16.of_int z;rt_work<-rt_work+2;i<-i+1;rt_work<-rt_work+2;rt_work<-rt_work+2;}\nrt_work<-rt_work+2305;return(output,rt_work);'
    if name=='trit':
        return 'rt_work<-2304;valid<-true;rt_work<-rt_work+1;i<-0;rt_work<-rt_work+1;rt_work<-rt_work+2;\nwhile(i<768){x<-coeff ap.[i];rt_work<-rt_work+2;v0<-(x = -1);rt_work<-rt_work+2;\nv1<-(x = 0);rt_work<-rt_work+2;v2<-(x = 1);rt_work<-rt_work+2;\nvalid<-valid /\\ (v0 \\/ v1 \\/ v2);rt_work<-rt_work+4;i<-i+1;rt_work<-rt_work+2;rt_work<-rt_work+2;}\nrt_work<-rt_work+1;return(valid,rt_work);'
    raise ValueError('unsupported manual word check')


def expected_sampler(qualified):
    if qualified=='RTPsiSampler.measure':
        return 'work<-0;random_bytes<-0;buf<$uniform192;work<-work+385;random_bytes<-random_bytes+192;\nscratch<-witness;work<-work+769;\nout<@RTFixedCBD.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(scratch,buf);\nwork<-work+out.`2+2308;work<-work+2305;return(out.`1,work,random_bytes);'
    if qualified=='RTKey32Sampler.measure':
        return 'work<-0;random_bytes<-0;key<$uniform32;work<-work+65;random_bytes<-random_bytes+32;\nwork<-work+97;return(key,work,random_bytes);'
    raise ValueError('unsupported sampled distribution')


def check_body(qualified, actual):
    if qualified.startswith('RTPrimitive.'):
        expected=expected_primitive(qualified.split('.')[1])
    elif qualified.startswith('RTFixedWordChecks.'):
        expected=expected_wordcheck(qualified.split('.')[1])
    elif qualified in ('RTPsiSampler.measure','RTKey32Sampler.measure'):
        expected=expected_sampler(qualified)
    elif qualified=='RTWordScale3.measure':
        expected=expected_scale()
    else:
        raise ValueError('manual calibrated endpoint has no independent charge rule: '+qualified)
    policy.require(normalize(actual)==normalize(expected), 'manual source/charge/loop coverage differs: '+qualified)


def check_header(qualified,actual):
    expected={
      'RTPrimitive.suffix':'proc suffix(x y:W8.t Array32.t):bool*int=',
      'RTPrimitive.cipher':'proc cipher(x y:W8.t Array1152.t):bool*int=',
      'RTPrimitive.key':'proc key(x y:fo_h_input):bool*int=',
      'RTPrimitive.word_equal':'proc word_equal(x y:W16.t Array768.t):bool*int=',
      'RTPrimitive.copy768':'proc copy768(x:W16.t Array768.t):W16.t Array768.t*int=',
      'RTWordScale3.measure':'proc measure(a:pke_poly):pke_poly*int=',
      'RTFixedWordChecks.normalize':'proc normalize(ap:W16.t Array768.t):(W16.t Array768.t)*int=',
      'RTFixedWordChecks.trit':'proc trit(ap:W16.t Array768.t):bool*int=',
      'RTPsiSampler.measure':'proc measure():pke_poly*int*int=',
      'RTKey32Sampler.measure':'proc measure():W8.t Array32.t*int*int='}
    policy.require(qualified in expected and policy.compact(actual)==policy.compact(expected[qualified]),
                   'manual array/return shape drift: '+qualified)


def check_contracts(source,text):
    import calibration_policy as cal
    declarations={}
    if source=='RTPrimitiveCost':
        formulas=('op rt_byte_compare_steps(n:int)=18*n+5.',
                  'op rt_word_compare_steps(n:int)=16*n+5.',
                  'op rt_copy_steps(n:int)=14*n+5.','op rt_key_compare_steps=2629.')
        for formula in formulas:
            policy.require(policy.compact(formula) in policy.compact(policy.without_comments(text)),'manual primitive price formula drift')
        for name,cost in (('suffix','rt_byte_compare_steps 32'),('cipher','rt_byte_compare_steps 1152'),
                          ('key','rt_key_compare_steps'),('word_equal','rt_word_compare_steps 768')):
            declarations['rt_primitive_'+name+'_correct']='x0 y0:phoare[RTPrimitive.'+name+':x=x0 /\\ y=y0 ==>res=((x0=y0),'+cost+')]=1%r.'
        declarations['rt_primitive_copy768_correct']='x0:phoare[RTPrimitive.copy768:x=x0 ==>res=(x0,rt_copy_steps 768)]=1%r.'
    elif source=='RTWordCodec':
        declarations={
         'rt_word_scale3_measure_projection':':equiv[RTWordScale3.measure~RTWordScale3.run:={a}==>res{1}.`1=res{2}].',
         'rt_word_scale3_measure_cost':':hoare[RTWordScale3.measure:true==>16132<=res.`2<=19204].'}
    elif source=='RTFixedWordChecks':
        for name,original,bound in (('normalize','RRecNormalize.run',16133),('trit','RRecTrit.check',14597)):
            declarations['rt_fixed_'+name+'_projection']=':equiv[RTFixedWordChecks.'+name+'~'+original+':={ap}==>res{1}.`1=res{2}].'
            declarations['rt_fixed_'+name+'_bound_cost']=':hoare[RTFixedWordChecks.'+name+':true==>0<=res.`2<=rt_fixed_'+name+'_bound].'
            policy.require('oprt_fixed_'+name+'_bound:int='+str(bound)+'.' in policy.compact(text),'manual word price drift')
    elif source=='RTPsiSampler':
        declarations={
         'rt_psi_sampler_law':':equiv[RTPsiSampler.run~RTPsiLaw.run:true==>={res}].',
         'rt_key32_sampler_law':':equiv[RTKey32Sampler.run~RTPsiLaw.key32:true==>={res}].',
         'rt_psi_sampler_measure_projection':':equiv[RTPsiSampler.measure~RTPsiSampler.run:true==>res{1}.`1=res{2}].',
         'rt_key32_sampler_measure_projection':':equiv[RTKey32Sampler.measure~RTKey32Sampler.run:true==>res{1}.`1=res{2}].',
         'rt_psi_sampler_measure_total':':hoare[RTPsiSampler.measure:true==>0<=res.`2+res.`3<=42636].',
         'rt_key32_sampler_measure_cost':':hoare[RTKey32Sampler.measure:true==>res.`2=162 /\\ res.`3=32 /\\ res.`2+res.`3=194].'}
    else:
        raise ValueError('unreviewed manual contract source')
    for name,decl in declarations.items():
        policy.require(cal.lemma_declaration(text,name)==policy.compact('lemma '+name+' '+decl),'manual endpoint/result/cost declaration drift: '+name)
    return len(declarations)


def check(require_complete=True):
    import model_contract
    checks=[('RTPrimitiveCost','RTPrimitive',name) for name in ('suffix','cipher','key','word_equal','copy768')]
    checks.append(('RTWordCodec','RTWordScale3','measure'))
    checks.extend([('RTFixedWordChecks','RTFixedWordChecks',name) for name in ('normalize','trit')])
    checks.extend([('RTPsiSampler',name,'measure') for name in ('RTPsiSampler','RTKey32Sampler')])
    endpoints=[];checked=set();contracts=0
    for source,module,proc in checks:
        path=policy.PROOF/('NTRUPlus768'+source+'.ec')
        if not path.is_file():
            policy.require(not require_complete,'missing manually calibrated source: '+source);continue
        matches=[(head,body) for m,block in model_contract.syntax.modules(path.read_text()) if m==module
                 for name,head,body,_i,_j in model_contract.syntax.procedures(block) if name==proc]
        policy.require(len(matches)==1,'manual procedure inventory differs')
        check_header(module+'.'+proc,matches[0][0]);check_body(module+'.'+proc,matches[0][1])
        endpoints.append(str(path.relative_to(policy.ROOT))+':'+module+'.'+proc)
        if source not in checked:
            contracts+=check_contracts(source,path.read_text());checked.add(source)
    distributions=policy.compact((policy.BASE/'kem_rom_oracle/NTRUPlus768ROMDistributions.ec').read_text())
    for n in (32,192):
        policy.require('dmap(dlistW8.dword'+str(n)+')(Array'+str(n)+'.of_listW8.zero)' in distributions,'fixed byte-product sampling rule changed')
    return {'status':'MANUAL_SOURCE_RULES_CHECKED','endpoints':endpoints,'exact_contracts':contracts,
            'scope':'Ten explicit word-scan/sampling templates; full kernel-composition coverage is checked separately.'}
