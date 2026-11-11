"""Independent array-copy and composed SimEncrypt source calibration."""
import json,re
import policy
import calibration_policy as cal
import manual_calibration as manual
import kernel_calibration as kernel


def check(require_complete=True):
    metadata=policy.TEST/'calibration/manual-sim.json'
    if not metadata.is_file():
        policy.require(not require_complete,'SimEncrypt source calibration pending');return {'status':'PENDING','endpoints':[]}
    d=json.loads(metadata.read_text());source=cal.path(d['file']);text=source.read_text()
    policy.require(policy.sha(source.read_bytes())==d['source_sha256'],'SimEncrypt calibrated source drift')
    values=dict(kernel.check(require_complete)['closed_bounds']);endpoints=[]
    shapes={'tail':(224,192,32,'h','32+i'),'peel':(1153,1152,1,'input','i+1')}
    policy.require({p['procedure'] for p in d['copy_procedures']}==set(shapes),'Sim copy inventory drift')
    for p in d['copy_procedures']:
        ni,no,offset,arg,index=shapes[p['procedure']]
        initial={'input_clone':3*ni,'scratch_alloc_and_transfer':no+1,'index_init':1,'guard':2}
        loop={'output_assignment':4,'index_increment':2,'guard':2};ret=3*no+1
        total=sum(initial.values())+no*sum(loop.values())+ret
        policy.require((p['input_cells'],p['output_cells'],p['index_offset'])==(ni,no,offset),'copy shape mismatch')
        policy.require(p['initial_costs']==initial and p['loop_costs']==loop and p['return_cost']==ret and p['current_bound']==total,'copy fee rule differs')
        expected=f'''work<-{3*ni};output<-witness;work<-work+{no+1};i<-0;work<-work+1;work<-work+2;
 while(i<{no}){{output.[i]<-{arg}.[{index}];work<-work+4;i<-i+1;work<-work+2;work<-work+2;}}
 work<-work+{ret};return(output,work);'''
        endpoint='RTKernelBytes.'+p['procedure']
        policy.require(manual.normalize(cal.raw_body(text,endpoint))==policy.compact(expected),'copy source/charge coverage drift')
        policy.require(re.search(r'\bop\s+'+p['bound_op']+r'\s*:\s*int\s*=\s*'+str(total)+r'\.',text),'copy bound operation drift')
        prefix='rt_kernel_'+p['procedure'];formal='h0' if arg=='h' else 'input0';value='complete_hash_tail h0' if arg=='h' else 'peel1153 input0'
        spec='lemma '+prefix+'_spec '+formal+' : hoare['+endpoint+':'+arg+'='+formal+' ==>res=('+value+','+p['bound_op']+')].'
        policy.require(cal.lemma_declaration(text,prefix+'_spec')==policy.compact(spec),'copy semantic result/cost contract drift')
        values[p['bound_op']]=total;endpoints.append(d['file']+':'+endpoint)
    # The eight concrete data-path calls are fixed independently of metadata.
    calls=[
     ('RTKernelBytes.tail',1,0,192,'rt_kernel_tail_bound'),
     ('RTFixedCBD.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1',2,768,768,'rt_fixed_cbd_bound'),
     ('RTFixedNTT.jade_ntruplus_ntruplus768_amd64_ref_ntt',2,768,768,'rt_fixed_ntt_bound'),
     ('RTFixedGPrepare.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare',3,2305,2305,'rt_fixed_gprepare_bound'),
     ('RTKernelBytes.peel',1,0,1152,'rt_kernel_peel_bound'),
     ('G.get',1,0,192,None),
     ('RTFixedSOTPEncode.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode',3,768,768,'rt_fixed_sotpencode_bound'),
     ('RTKernelPKEEnc.run',3,0,1152,'rt_kernel_pkeenc_bound')]
    sim=d['sim_encrypt'];policy.require(len(sim['calls'])==len(calls),'SimEncrypt call omission')
    fees=[]
    for record,(target,arity,scratch,result,bound) in zip(sim['calls'],calls):
        fee=2+arity+scratch+3*result
        policy.require(record=={'procedure':target,'arity':arity,'scratch_cells':scratch,'result_cells':result,'caller_cost':fee,'callee_bound_op':bound},'SimEncrypt source call/frame drift')
        fees.append(fee)
    entry=3*(1152+96+224);ret=3*1152+1
    expected=f'''work<-{entry};
 bt<@RTKernelBytes.tail(hout);tail<-bt.`1;work<-work+bt.`2+{fees[0]};
 poly<@RTFixedCBD.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,tail);r<-poly.`1;work<-work+poly.`2+{fees[1]};
 poly<@RTFixedNTT.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);rhat<-poly.`1;work<-work+poly.`2+{fees[2]};
 prepared<@RTFixedGPrepare.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(witness,witness,rhat);
 (serialized,input)<-prepared.`1;work<-work+prepared.`2+{fees[3]};
 bq<@RTKernelBytes.peel(input);payload<-bq.`1;work<-work+bq.`2+{fees[4]};
 bt<@G.get(payload);pad<-bt.`1;backend<-bt.`2;work<-work+backend+{fees[5]};
 poly<@RTFixedSOTPEncode.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(witness,msg,pad);
 code<-poly.`1;work<-work+poly.`2+{fees[6]};
 ciphertext<@RTKernelPKEEnc.run(pk,code,r);ct<-ciphertext.`1;work<-work+ciphertext.`2+{fees[7]};
 work<-work+{ret};return(ct,work,backend);'''
    policy.require(manual.normalize(cal.raw_body(text,'RTKernelSimEncrypt.run'))==policy.compact(expected),'SimEncrypt instruction/counter drift')
    total=entry+ret+sum(fees)+sum(values[b] for _t,_a,_s,_r,b in calls if b)
    policy.require(sim['entry_cells']==1472 and sim['entry_cost']==entry and sim['result_cells']==1152 and sim['return_cost']==ret and sim['current_bound']==total,'SimEncrypt aggregate source bound drift')
    op=re.search(r'\bop\s+rt_kernel_sim_encrypt_bound\s*:\s*int\s*=([^.]*)\.',text)
    policy.require(op and kernel.numeric(op.group(1).strip(),values)==total,'actual SimEncrypt cost op drift')
    contracts={
     'rt_kernel_sim_encrypt_projection':'(G<:RTKernelCostGPort):equiv[RTKernelSimEncrypt(G).run~SimEncrypt(RTKernelGValue(G)).run:={arg,glob G}==>res{1}.`1=res{2}/\\={glob G}].',
     'rt_kernel_sim_encrypt_local_cost':'(G<:RTKernelCostGPort):hoare[RTKernelSimEncrypt(G).run:true==>0<=res.`2-res.`3<=rt_kernel_sim_encrypt_bound].',
     'rt_kernel_g_projection':'(G<:RTKernelCostGPort):equiv[G.get~RTKernelGValue(G).get:={arg,glob G}==>res{1}.`1=res{2}/\\={glob G}].'}
    for name,decl in contracts.items():
        policy.require(cal.lemma_declaration(text,name)==policy.compact('lemma '+name+decl),'SimEncrypt semantic/backend contract drift')
    adapter='out<@G.get(input);return out.`1;'
    policy.require(manual.normalize(cal.raw_body(text,'RTKernelGValue.get'))==policy.compact(adapter),'G-value projection changes backend call')
    endpoints.extend([d['file']+':RTKernelSimEncrypt.run',d['file']+':RTKernelGValue.get'])
    values['rt_kernel_sim_encrypt_bound']=total
    return {'status':'SIM_SOURCE_FEES_RECONSTRUCTED','endpoints':endpoints,'local_cost':total,'backend_cost':'separate actual G.get result; must be closed by phase calibration','closed_bounds':values}
